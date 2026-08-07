/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/tools.scala

Service registration for `isabelle ic2` and the `isabelle ic2_test` runner.
*/

package isabelle.ic2

import isabelle._

class Tools extends Isabelle_Scala_Tools(
  IC2.isabelle_tool,
  Test_Tool.isabelle_tool)
