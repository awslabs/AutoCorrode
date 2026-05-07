/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import ToolArgs._

/** Handler for the `web_search` tool. Thin HTTPS client against DuckDuckGo's
  * lite endpoint; no authentication, no cookies, no JavaScript. Results are
  * extracted from the rendered HTML with a regex because DDG lite has no
  * structured API.
  *
  * Kept in its own file because it's the one tool in the registry that has
  * zero coupling to Isabelle/jEdit, Bedrock, or I/Q — isolating it keeps
  * network code out of the main AssistantTools bundle and makes sandboxed
  * replacement (e.g. for enterprise proxies) straightforward.
  */
private[assistant] object WebSearchToolHandler {
  // A safety cap: we don't want to spend a whole tool-use iteration on a
  // hostile page whose <a> hrefs try to exhaust us. 2x the requested count
  // is plenty of headroom to skip the DDG internal self-links.
  private val MAX_LINK_SCAN_MULTIPLIER = 2

  // Cap on the response body we'll accept. DDG lite pages are ~100 KB at
  // most; 2 MB leaves a ton of headroom while bounding worst-case memory
  // from a misbehaving or hostile endpoint.
  private val MAX_RESPONSE_BYTES: Int = 2 * 1024 * 1024

  // Require whitespace or the opening `<a` before `href=` so that attribute
  // names ending in `href` (e.g. `data-href="…"`) cannot match as if they
  // were the canonical `href`. The leading `[^>]*` consumes earlier
  // attributes without allowing `>`.
  private val linkPattern = """<a[^>]*\s+href="([^"]+)"[^>]*>([^<]+)</a>""".r

  private val connectTimeout = java.time.Duration.ofSeconds(10)
  private val requestTimeout = java.time.Duration.ofSeconds(10)

  def execWebSearch(args: ResponseParser.ToolArgs): String = {
    val query = safeStringArg(args, "query", MAX_PATTERN_ARG_LENGTH)
    if (query.isEmpty) "Error: query required"
    else {
      val maxResults = math.min(10, math.max(1, intArg(args, "max_results", 5)))
      try {
        val encodedQuery = java.net.URLEncoder.encode(query, "UTF-8")
        val url = s"https://lite.duckduckgo.com/lite/?q=$encodedQuery"

        val client = java.net.http.HttpClient
          .newBuilder()
          .connectTimeout(connectTimeout)
          .followRedirects(java.net.http.HttpClient.Redirect.NORMAL)
          .build()
        val request = java.net.http.HttpRequest
          .newBuilder()
          .uri(java.net.URI.create(url))
          .timeout(requestTimeout)
          .GET()
          .build()

        val html = fetchBodyBounded(client, request)

        val results = scala.collection.mutable.ListBuffer[String]()

        import scala.util.boundary, boundary.break
        boundary {
          for (m <- linkPattern.findAllMatchIn(html).take(maxResults * MAX_LINK_SCAN_MULTIPLIER)) {
            val href = m.group(1)
            val title = m.group(2).trim
            if (!href.startsWith("//duckduckgo.com") && title.nonEmpty) {
              results += s"$title\n  URL: $href"
            }
            if (results.length >= maxResults) break()
          }
        }

        if (results.nonEmpty) results.mkString("\n\n")
        else s"No search results found for: $query"
      } catch {
        case ex: Exception => s"Web search error: ${ex.getMessage}"
      }
    }
  }

  /** Stream the response body into memory with a hard byte cap. Beyond the
    * cap we abort and surface a clear error rather than let a hostile or
    * buggy endpoint blow through the JVM heap. */
  private def fetchBodyBounded(
      client: java.net.http.HttpClient,
      request: java.net.http.HttpRequest
  ): String = {
    val response = client.send(
      request,
      java.net.http.HttpResponse.BodyHandlers.ofInputStream()
    )
    val stream = response.body()
    try {
      val buf = new Array[Byte](8192)
      val out = new java.io.ByteArrayOutputStream()
      var total = 0
      var n = stream.read(buf)
      while (n >= 0) {
        total += n
        if (total > MAX_RESPONSE_BYTES)
          throw new java.io.IOException(
            s"response body exceeded cap of $MAX_RESPONSE_BYTES bytes"
          )
        out.write(buf, 0, n)
        n = stream.read(buf)
      }
      out.toString("UTF-8")
    } finally stream.close()
  }
}
