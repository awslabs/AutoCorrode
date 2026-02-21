/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatest.BeforeAndAfterEach
import scala.util.Success

class ErrorHandlerExtendedTest extends AnyFunSuite with Matchers with BeforeAndAfterEach {
  
  override def beforeEach(): Unit = {
    ErrorHandler.cleanupAll()
  }
  
  test("withErrorHandling should handle successful operations") {
    val result = ErrorHandler.withErrorHandling("test operation") { "success" }
    result shouldBe Success("success")
  }
  
  test("withErrorHandling should handle exceptions") {
    val result = ErrorHandler.withErrorHandling("test operation") {
      throw new RuntimeException("test error")
    }
    result.isFailure shouldBe true
    result.failed.get.getMessage should include("test error")
  }
  
  test("withErrorHandling elapsed limit should fail after slow operation") {
    val result = ErrorHandler.withErrorHandling("test operation", Some(100L)) {
      Thread.sleep(200)
      "should exceed limit"
    }
    result.isFailure shouldBe true
    result.failed.get.getMessage should include("exceeded elapsed limit")
  }
  
  test("withManagedResource should properly cleanup resources") {
    class TestResource extends AutoCloseable {
      var closed = false
      def close(): Unit = closed = true
    }
    var resource: TestResource = null
    val result = ErrorHandler.withManagedResource(new TestResource()) { r =>
      resource = r; "success"
    }
    result shouldBe Success("success")
    resource.closed shouldBe true
  }
  
  test("resource registry should track and cleanup resources") {
    class TestResource extends AutoCloseable {
      var closed = false
      def close(): Unit = closed = true
    }
    val resource = new TestResource()
    ErrorHandler.registerResource(resource)
    ErrorHandler.cleanupAll()
    resource.closed shouldBe true
  }
}
