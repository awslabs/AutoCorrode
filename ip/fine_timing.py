"""Decode and aggregate fine-grained timing reports from PIDE exports."""

from dataclasses import dataclass, field
import math


X = "\x05"
Y = "\x06"
REPORT_MARKUP = "fine_grained_timing"
ENTRY_MARKUP = "fine_grained_timing_entry"
BUCKET_MARKUP = "fine_grained_timing_bucket"
SUPPORTED_VERSIONS = (1, 2)


@dataclass
class YXMLNode:
    name: str
    properties: dict
    body: list = field(default_factory=list)


@dataclass
class Timing:
    elapsed_us: int
    cpu_us: int
    gc_us: int


@dataclass
class Aggregate:
    count: int
    timing: Timing
    min_elapsed_us: int
    max_elapsed_us: int
    histogram: dict


@dataclass
class Sample:
    name: str
    success: bool
    aggregate: Aggregate


@dataclass
class Invocation:
    version: int
    invocation: int
    method: str
    success: bool
    timing: object
    samples: list
    raised: bool = False
    theory: str = ""
    export_name: str = ""
    command: str = ""
    command_offset: object = None
    source_file: str = ""
    line: object = None
    proof: str = ""


@dataclass
class DecodeResult:
    invocations: list = field(default_factory=list)
    malformed: int = 0
    unsupported: int = 0
    duplicates: int = 0
    superseded: int = 0
    decode_failures: list = field(default_factory=list)


class YXMLError(ValueError):
    pass


class ReportError(ValueError):
    pass


class UnsupportedVersion(ReportError):
    pass


def parse_yxml(text):
    """Parse a YXML body into text strings and ``YXMLNode`` values."""
    roots = []
    stack = [roots]
    for chunk in text.split(X):
        if chunk.startswith(Y):
            fields = chunk[1:].split(Y)
            if fields == [""]:
                if len(stack) == 1:
                    raise YXMLError("unbalanced element close")
                stack.pop()
            else:
                name = fields[0]
                if not name:
                    raise YXMLError("empty element name")
                properties = {}
                for item in fields[1:]:
                    if "=" not in item:
                        raise YXMLError("malformed element property")
                    key, value = item.split("=", 1)
                    if not key or key in properties:
                        raise YXMLError("invalid element property")
                    properties[key] = value
                node = YXMLNode(name, properties)
                stack[-1].append(node)
                stack.append(node.body)
        elif chunk:
            stack[-1].append(chunk)
    if len(stack) != 1:
        raise YXMLError("unclosed element")
    return roots


def _nodes(body):
    return [item for item in body if isinstance(item, YXMLNode)]


def _entry_children(body):
    return [
        child for child in body
        if isinstance(child, YXMLNode)
        and child.name == ENTRY_MARKUP
    ]


def _property(properties, name):
    if name not in properties:
        raise ReportError(f"missing property {name}")
    return properties[name]


def _integer(properties, name, minimum=None):
    text = _property(properties, name)
    try:
        value = int(text)
    except ValueError as ex:
        raise ReportError(f"invalid integer property {name}") from ex
    if minimum is not None and value < minimum:
        raise ReportError(f"property {name} is below {minimum}")
    return value


def _boolean(properties, name):
    value = _property(properties, name)
    if value == "true":
        return True
    if value == "false":
        return False
    raise ReportError(f"invalid boolean property {name}")


def _timing(properties):
    return Timing(
        elapsed_us=_integer(properties, "elapsed_us"),
        cpu_us=_integer(properties, "cpu_us"),
        gc_us=_integer(properties, "gc_us"),
    )


def _decode_sample(node):
    if node.name != ENTRY_MARKUP:
        raise ReportError(f"unexpected report body element {node.name}")
    properties = node.properties
    count = _integer(properties, "count", 1)
    histogram = {}
    for bucket_node in _nodes(node.body):
        if bucket_node.name != BUCKET_MARKUP or _nodes(bucket_node.body):
            raise ReportError("malformed histogram bucket")
        bucket = _integer(bucket_node.properties, "bucket", 0)
        bucket_count = _integer(bucket_node.properties, "count", 1)
        if bucket in histogram:
            raise ReportError("duplicate histogram bucket")
        histogram[bucket] = bucket_count
    if sum(histogram.values()) != count:
        raise ReportError("histogram count does not match sample count")
    timing = _timing(properties)
    minimum = _integer(properties, "min_elapsed_us")
    maximum = _integer(properties, "max_elapsed_us")
    return Sample(
        name=_property(properties, "name"),
        success=_boolean(properties, "success"),
        aggregate=Aggregate(
            count=count,
            timing=timing,
            min_elapsed_us=minimum,
            max_elapsed_us=maximum,
            histogram=histogram,
        ),
    )


def _normalize_report_body(body):
    nodes = _nodes(body)
    if len(body) == 1 and isinstance(body[0], str) and X in body[0]:
        return parse_yxml(body[0])
    return nodes


def decode_report(properties, body):
    version = _integer(properties, "version")
    if version not in SUPPORTED_VERSIONS:
        raise UnsupportedVersion(f"unsupported report version {version}")
    timing_names = ("elapsed_us", "cpu_us", "gc_us")
    timing = (
        _timing(properties)
        if version == 1 or any(name in properties for name in timing_names)
        else None
    )
    return Invocation(
        version=version,
        invocation=_integer(properties, "invocation"),
        method=_property(properties, "method"),
        success=_boolean(properties, "success"),
        timing=timing,
        raised=(
            _boolean(properties, "raised")
            if "raised" in properties else False
        ),
        samples=[
            _decode_sample(node) for node in _normalize_report_body(body)
        ],
    )


def _command_location(ancestors):
    for node in reversed(ancestors):
        if node.name != "command_span":
            continue
        command = node.properties.get("name", "")
        stack = list(reversed(_nodes(node.body)))
        while stack:
            child = stack.pop()
            offset = child.properties.get("command_offset")
            if offset is not None:
                try:
                    return command, int(offset)
                except ValueError:
                    return command, None
            stack.extend(reversed(_nodes(child.body)))
        return command, None
    return "", None


def _walk(body, ancestors=()):
    stack = [
        (item, ancestors) for item in reversed(body)
        if isinstance(item, YXMLNode)
    ]
    while stack:
        item, parents = stack.pop()
        yield item, parents
        child_parents = parents + (item,)
        stack.extend(
            (child, child_parents) for child in reversed(item.body)
            if isinstance(child, YXMLNode)
        )


def extract_reports(text, theory="", export_name=""):
    """Decode all transported timing reports in one PIDE markup export."""
    result = DecodeResult()
    if REPORT_MARKUP not in text:
        return result
    try:
        body = parse_yxml(text)
    except YXMLError:
        result.malformed += 1
        return result

    seen = set()
    superseded = {}
    for node, ancestors in _walk(body):
        properties = None
        report_body = None
        if (node.name == "xml_elem" and
                node.properties.get("xml_name") == REPORT_MARKUP):
            properties = {
                key: value for key, value in node.properties.items()
                if key != "xml_name"
            }
            bodies = [
                child for child in _nodes(node.body)
                if child.name == "xml_body"
            ]
            if len(bodies) != 1:
                result.malformed += 1
                continue
            report_body = bodies[0].body
        elif node.name == REPORT_MARKUP:
            properties = node.properties
            report_body = node.body
        if properties is None:
            continue

        try:
            report_body = _entry_children(
                _normalize_report_body(report_body))
            invocation = decode_report(properties, report_body)
        except UnsupportedVersion:
            result.unsupported += 1
            continue
        except (ReportError, YXMLError):
            result.malformed += 1
            continue

        invocation.theory = theory
        invocation.export_name = export_name
        invocation.command, invocation.command_offset = _command_location(
            ancestors)
        key = (
            theory, invocation.invocation, invocation.method,
            invocation.success, invocation.raised,
            invocation.command_offset,
            _timing_extent(invocation),
            tuple(
                (sample.name, sample.success, sample.aggregate.count,
                 sample.aggregate.timing.elapsed_us,
                 sample.aggregate.timing.cpu_us,
                 sample.aggregate.timing.gc_us,
                 sample.aggregate.min_elapsed_us,
                 sample.aggregate.max_elapsed_us,
                 tuple(sorted(sample.aggregate.histogram.items())))
                for sample in invocation.samples
            ),
        )
        if key in seen:
            result.duplicates += 1
            continue
        seen.add(key)

        # A profile re-reports as its caller pulls more results, and each is a
        # complete snapshot of the accumulator rather than an increment. The
        # snapshots differ, so the content key above does not collapse them;
        # keeping them all would count the same samples repeatedly. Retain the
        # largest snapshot per invocation instead.
        identity = (
            theory, invocation.invocation, invocation.method,
            invocation.command_offset,
        )
        previous_index = superseded.get(identity)
        if previous_index is None:
            superseded[identity] = len(result.invocations)
            result.invocations.append(invocation)
        elif _snapshot_extent(invocation) > _snapshot_extent(
                result.invocations[previous_index]):
            result.invocations[previous_index] = invocation
            result.superseded += 1
        else:
            result.superseded += 1
    return result


def _snapshot_extent(invocation):
    """Order snapshots of one invocation; the largest is the final one."""
    outcome = (
        2 if invocation.raised
        else 1 if invocation.success
        else 0
    )
    return (
        sum(sample.aggregate.count for sample in invocation.samples),
        outcome,
        _timing_extent(invocation),
        sum(sample.aggregate.timing.elapsed_us
            for sample in invocation.samples),
    )


def _timing_extent(invocation):
    timing = invocation.timing
    if timing is None:
        return (-1, -1, -1)
    return (timing.elapsed_us, timing.cpu_us, timing.gc_us)


def merge_aggregate(left, right):
    histogram = dict(left.histogram)
    for bucket, count in right.histogram.items():
        histogram[bucket] = histogram.get(bucket, 0) + count
    return Aggregate(
        count=left.count + right.count,
        timing=Timing(
            elapsed_us=left.timing.elapsed_us + right.timing.elapsed_us,
            cpu_us=left.timing.cpu_us + right.timing.cpu_us,
            gc_us=left.timing.gc_us + right.timing.gc_us,
        ),
        min_elapsed_us=min(left.min_elapsed_us, right.min_elapsed_us),
        max_elapsed_us=max(left.max_elapsed_us, right.max_elapsed_us),
        histogram=histogram,
    )


def percentile_upper_bound(aggregate, fraction):
    if aggregate.count <= 0 or not aggregate.histogram:
        return 0
    target = max(1, math.ceil(max(0.0, min(1.0, fraction)) *
                              aggregate.count))
    accumulated = 0
    selected = max(aggregate.histogram)
    for bucket, count in sorted(aggregate.histogram.items()):
        accumulated += count
        if accumulated >= target:
            selected = bucket
            break
    return (1 << (selected + 1)) - 1 if selected < 62 else (1 << 63) - 1


def aggregate_invocations(invocations, group_key):
    rows = {}
    for invocation in invocations:
        group = group_key(invocation)
        for sample in invocation.samples:
            key = (group, sample.name, sample.success)
            if key in rows:
                rows[key] = merge_aggregate(rows[key], sample.aggregate)
            else:
                rows[key] = sample.aggregate
    return rows


def aggregate_to_json(aggregate):
    return {
        "count": aggregate.count,
        "timing_us": {
            "elapsed": aggregate.timing.elapsed_us,
            "cpu": aggregate.timing.cpu_us,
            "gc": aggregate.timing.gc_us,
            "min_elapsed": aggregate.min_elapsed_us,
            "max_elapsed": aggregate.max_elapsed_us,
        },
        "percentile_upper_bound_us": {
            "p50": percentile_upper_bound(aggregate, 0.50),
            "p90": percentile_upper_bound(aggregate, 0.90),
            "p99": percentile_upper_bound(aggregate, 0.99),
        },
        "histogram": {
            str(bucket): count
            for bucket, count in sorted(aggregate.histogram.items())
        },
    }
