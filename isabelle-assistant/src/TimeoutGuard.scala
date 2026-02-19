/** Utility for scheduling non-blocking timeouts for Futures. Used to avoid
  * blocking entire threads in time-bound PIDE operations.
  */
package isabelle.assistant

import java.util.concurrent.{
  Executors,
  ScheduledExecutorService,
  TimeUnit,
  TimeoutException
}
import scala.concurrent.{Future, Promise}
import scala.concurrent.duration.FiniteDuration

object TimeoutGuard {
  // A single daemon thread for scheduling timeouts across the assistant
  private val scheduler: ScheduledExecutorService =
    Executors.newScheduledThreadPool(
      1,
      (r: Runnable) => {
        val t = new Thread(r, "assistant-timeout-scheduler")
        t.setDaemon(true)
        t
      }
    )

  /** Schedule a task to complete the promise with a TimeoutException after the
    * specified duration. Returns a function to cancel the scheduled timeout
    * task.
    */
  def scheduleTimeout[T](
      p: Promise[T],
      timeoutMs: Long,
      timeoutMsg: String = "Operation timed out"
  ): () => Unit = {
    val task = scheduler.schedule(
      new Runnable {
        def run(): Unit =
          p.tryFailure(new TimeoutException(timeoutMsg))
      },
      timeoutMs,
      TimeUnit.MILLISECONDS
    )

    // Return cancellation thunk
    () => task.cancel(false)
  }
}
