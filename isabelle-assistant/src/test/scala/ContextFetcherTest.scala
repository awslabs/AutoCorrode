/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Threading contract for [[ContextFetcher]]. Both `getContext` and
  * `extractEntities` run through the I/Q MCP backplane (a synchronous HTTP
  * call) and must never be invoked on the EDT — doing so used to freeze
  * jEdit for seconds while "Suggest name" waited on the response. These
  * tests pin the guard so a regression surfaces as a test failure rather
  * than a live GUI freeze. */
class ContextFetcherTest extends AnyFunSuite with Matchers {

  /** Run `body` on the Swing EDT and return whatever it produces.
    * Exceptions from the body propagate synchronously on the caller thread
    * through `scala.util.Try`, so test failures surface as assertion
    * failures rather than being swallowed. */
  private def onEdt[T](body: => T): T = {
    val result = new java.util.concurrent.atomic.AtomicReference[scala.util.Try[T]](null)
    javax.swing.SwingUtilities.invokeAndWait(() => {
      result.set(scala.util.Try(body))
    })
    result.get().get
  }

  test("extractEntities returns Nil when called on the EDT, does not block") {
    // Passing null buffer/offset would NPE if the guard didn't trip first.
    // The guard short-circuits so the call returns Nil harmlessly.
    val start = System.currentTimeMillis()
    val result = onEdt {
      ContextFetcher.extractEntities(null, 0)
    }
    val elapsed = System.currentTimeMillis() - start
    result shouldBe Nil
    // The guard must return synchronously. If the underlying MCP call ran
    // we'd see seconds of blocking; assert we're well under any plausible
    // network timeout.
    elapsed should be < 500L
  }

  test("getContext returns None when called on the EDT") {
    // Same contract as extractEntities. We can't easily construct a live
    // View in a unit test, but the guard fires before any view access.
    val result = onEdt {
      ContextFetcher.getContext(null, 1000)
    }
    result shouldBe None
  }
}
