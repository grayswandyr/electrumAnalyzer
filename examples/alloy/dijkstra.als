module examples/algorithms/dijkstra

/*
 * Models how mutexes are grabbed and released by processes, and
 * how Dijkstra8s mutex ordering criterion can prevent deadlocks.
 *
 * For a detailed description, see:
 *   E. W. Dijkstra, Cooperating sequential processes. Technological
 *   University, Eindhoven, The Netherlands, September 1965.
 *   Reprinted in Programming Languages, F. Genuys, Ed., Academic
 *   Press, New York, 1968, 43-112.
 *
 * Acknowledgements to Ulrich Geilmann for finding and fixing a bug
 * in the GrabMutex predicate.
 *   
 */

open util/ordering [State] as so
open util/ordering [Mutex] 

sig Process {}
sig Mutex {}

sig State { holds, waits: Process -> Mutex }


pred Initial [s: State]  { no s.holds + s.waits }

pred IsFree [s: State, m: Mutex] {
   // no process holds this mutex
   no m.~(s.holds)
   // all p: Process | m !in p.(this.holds)
}

pred IsStalled [s: State, p: Process] { some p.(s.waits) }

pred GrabMutex [s: State, p: Process, m: Mutex, s8: State] {
   // a process can only act if it is not
   // waiting for a mutex
   !IsStalled[s,p]
   // can only grab a mutex we do not yet hold
   m !in p.(s.holds)
   // mutexes are grabbed in order
   all m8: p.(s.holds) | so/lt[m8,m]
   IsFree[s,m] => {
      // if the mutex is free, we now hold it,
      // and do not become stalled
      p.(s8.holds) = p.(s.holds) + m
      no p.(s8.waits)
   } else {
    // if the mutex was not free,
    // we still hold the same mutexes we held,
    // and are now waiting on the mutex
    // that we tried to grab.
    p.(s8.holds) = p.(s.holds)
    p.(s8.waits) = m
  }
  all otherProc: Process - p | {
     otherProc.(s8.holds) = otherProc.(s.holds)
     otherProc.(s8.waits) = otherProc.(s.waits)
  }
}

pred ReleaseMutex [s: State, p: Process, m: Mutex, s8: State] {
   !IsStalled[s,p]
   m in p.(s.holds)
   p.(s8.holds) = p.(s.holds) - m
   no p.(s8.waits)
   no m.~(s.waits) => {
      no m.~(s8.holds)
      no m.~(s8.waits)
   } else {
      some lucky: m.~(s.waits) | {
        m.~(s8.waits) = m.~(s.waits) - lucky
        m.~(s8.holds) = lucky
      }
   }
  all mu: Mutex - m {
    mu.~(s8.waits) = mu.~(s.waits)
    mu.~(s8.holds)= mu.~(s.holds)
  }
}

// for every adjacent (pre,post) pair of States,
// one action happens: either some process grabs a mutex,
// or some process releases a mutex,
// or nothing happens (have to allow this to show deadlocks)
pred GrabOrRelease  {
    Initial[so/first] &&
    (
    all pre: State - so/last  | let post = so/next [pre] |
       (post.holds = pre.holds && post.waits = pre.waits)
        ||
       (some p: Process, m: Mutex | GrabMutex [pre, p, m, post])
        ||
       (some p: Process, m: Mutex | ReleaseMutex [pre, p, m, post])

    )
}

pred Deadlock  {
         some Process
         some s: State | all p: Process | some p.(s.waits)
}

assert DijkstraPreventsDeadlocks {
   GrabOrRelease => ! Deadlock
}


pred ShowDijkstra  {
    GrabOrRelease && Deadlock
    some waits
}

run Deadlock for 3 expect 1
run ShowDijkstra for 5 State, 2 Process, 2 Mutex expect 1
check DijkstraPreventsDeadlocks for 5 State, 5 Process, 4 Mutex expect 0
