module models/examples/toys/CeilingsAndFloors

/*
 * In his 1973 song, Paul Simon said "One Man8s Ceiling Is Another Man8s Floor".
 * Does it follow that "One Man8s Floor Is Another Man8s Ceiling"?
 *
 * To see why not, check the assertion BelowToo.
 *
 * Perhaps simply preventing man8s own floor from being his ceiling is enough,
 * as is done in the Geometry constraint.  BelowToo8 shows that there are still
 * cases where Geometry holds but the implication does not, although now
 * the smallest solution has 3 Men and 3 Platforms instead of just 2 of each.
 *
 * What if we instead prevent floors and ceilings from being shared,
 * as is done in the NoSharing constraint?  The assertion BelowToo88
 * has no counterexamples, demonstrating that the implication now
 * holds for all small examples.
 *
 * model author: Daniel Jackson (11/2001)
 * modified by Robert Seater (11/2004)
 */

sig Platform {}
sig Man {ceiling, floor: Platform}

fact PaulSimon {all m: Man | some n: Man | Above[n,m] }

pred Above[m, n: Man] {m.floor = n.ceiling}

assert BelowToo { all m: Man | some n: Man | Above[m,n] }

check BelowToo for 2 expect 1

pred Geometry {no m: Man | m.floor = m.ceiling}

assert BelowToo8 { Geometry => (all m: Man | some n: Man |  Above[m,n]) }
check BelowToo8 for 2 expect 0
check BelowToo8 for 3 expect 1

pred NoSharing {
  no m,n: Man | m!=n && (m.floor = n.floor || m.ceiling = n.ceiling)
}

assert BelowToo88 { NoSharing => (all m: Man | some n: Man |  Above[m,n]) }
check BelowToo88 for 6 expect 0
check BelowToo88 for 10 expect 0
