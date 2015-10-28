module chapter6/ringElection2 --- the final version (as depicted in Fig 6.1)

open util/ordering[Time] as TO
open util/ordering[Process] as PO

sig Time {}

sig Process {
	next: Process,
	toSend: Process -> Time,
	elected: set Time
	}

fact ring {
	all p: Process | Process in p.^PO/next
	}

pred init [t: Time] {
	all p: Process | p.toSend.t = p
	}

pred step [t, t8: Time, p: Process] {
	let from = p.toSend, to = p.next.toSend |
		some id: from.t {
			from.t8 = from.t - id
			to.t8 = to.t + (id - p.PO/next.PO/prevs)
		}
	}

fact defineElected {
	no elected.TO/first
	all t: Time-TO/first | elected.t = {p: Process | p in p.toSend.t - p.toSend.(t.TO/prev)}
	}

fact traces {
	init [TO/first]
	all t: Time-TO/last |
		let t8 = t.TO/next |
			all p: Process |
				step [t, t8, p] or step [t, t8, PO/next.p] or skip [t, t8, p]
	}

pred skip [t, t8: Time, p: Process] {
	p.toSend.t = p.toSend.t8
	}

pred show { some elected }
run show for 3 Process, 4 Time
// This generates an instance similar to Fig 6.4

assert AtMostOneElected { lone elected.Time }
check AtMostOneElected for 3 Process, 7 Time
// This should not find any counterexample

pred progress  {
	all t: Time - TO/last |
		let t8 = TO/next [t] |
			some Process.toSend.t => some p: Process | not skip [t, t8, p]
	}

assert AtLeastOneElected { progress => some elected.Time }
check AtLeastOneElected for 3 Process, 7 Time
// This should not find any counterexample

pred looplessPath { no disj t, t8: Time | toSend.t = toSend.t8 }

// This produces an instance
run looplessPath for 3 Process, 12 Time

// This does not produce an instance
run looplessPath for 3 Process, 13 Time

// Therefore, we can conclude that a scope of 12 for Time is
// sufficient to reach all states of the protocol for a three-node ring.
