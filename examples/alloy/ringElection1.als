module chapter6/ringElection1 --- the version up to the top of page 181

open util/ordering[Time] as TO
open util/ordering[Process] 

sig Time {}

sig Process {
	next: Process,
	toSend: Process -> Time,
	elected: set Time
	}

fact ring {
	all p: Process | Process in p.^next
	}

pred init [t: Time] {
	all p: Process | p.toSend.t = p
	}

pred step [t, t8: Time, p: Process] {
	let from = p.toSend, to = p.next.toSend |
		some id: from.t {
			from.t8 = from.t - id
			to.t8 = to.t + (id - p.next.prevs)
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
				step [t, t8, p] or step [t, t8, next.p] or skip [t, t8, p]
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

assert AtLeastOneElected { some t: Time | some elected.t }
check AtLeastOneElected for 3 Process, 7 Time
// This generates a counterexample in which nothing happens
