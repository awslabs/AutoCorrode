/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._

object IQArgumentUtilsTest {
  private def requireThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  def main(args: Array[String]): Unit = {
    val input: Map[String, JSON.T] = Map(
      "small_int" -> 42.0,
      "large_int" -> 1234567890123.0,
      "decimal" -> 12.75,
      "flag" -> true,
      "name" -> "alpha",
      "nested" -> Map("x" -> 7.0, "y" -> "z"),
      "list" -> List(1.0, 2.5, "v")
    )

    val argsMap = IQArgumentUtils.extractArguments(input)

    requireThat(argsMap("small_int").isInstanceOf[Double], "small_int should remain numeric Double")
    requireThat(argsMap("large_int").isInstanceOf[Double], "large_int should remain numeric Double")
    requireThat(argsMap("decimal").isInstanceOf[Double], "decimal should remain numeric Double")
    requireThat(argsMap("large_int").asInstanceOf[Double] == 1234567890123.0, "large_int value changed")
    requireThat(argsMap("decimal").asInstanceOf[Double] == 12.75, "decimal value changed")

    requireThat(argsMap("nested").isInstanceOf[Map[_, _]], "nested object should remain map")
    requireThat(argsMap("list").isInstanceOf[List[_]], "list should remain list")

    val intOk = IQArgumentUtils.optionalIntParam(argsMap, "small_int")
    requireThat(intOk == Right(Some(42)), s"expected small_int parse success, got $intOk")

    val longOk = IQArgumentUtils.optionalLongParam(argsMap, "large_int")
    requireThat(longOk == Right(Some(1234567890123L)), s"expected large_int parse success, got $longOk")

    val decimalErr = IQArgumentUtils.optionalIntParam(argsMap, "decimal")
    requireThat(decimalErr.isLeft, s"decimal integer parse should fail, got $decimalErr")
    requireThat(decimalErr.left.get.contains("decimal"), s"decimal error should reference parameter, got $decimalErr")

    val outOfRangeInt = IQArgumentUtils.optionalIntParam(Map("x" -> 3000000000.0), "x")
    requireThat(outOfRangeInt.isLeft, s"out-of-range int should fail, got $outOfRangeInt")
    requireThat(outOfRangeInt.left.get.contains("Int range"), s"out-of-range error should mention Int range, got $outOfRangeInt")

    val missingRequired = IQArgumentUtils.requiredIntParam(Map.empty, "start_line")
    requireThat(missingRequired.isLeft, "missing required int should fail")
    requireThat(missingRequired.left.get.contains("start_line"), "missing required message should reference parameter")

    println("IQArgumentUtilsTest passed")
  }
}
