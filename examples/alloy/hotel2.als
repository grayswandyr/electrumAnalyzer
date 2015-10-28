module chapter6/hotel2 --- the final model in Fig 6.7

open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Key {}
sig Time {}

sig Room {
	keys: set Key,
	currentKey: keys one -> Time
	}

fact DisjointKeySets {
	-- each key belongs to at most one room
	Room<:keys   in   Room lone-> Key
	}

one sig FrontDesk {
	lastKey: (Room -> lone Key) -> Time,
	occupant: (Room -> Guest) -> Time
	}

sig Guest {
	keys: Key -> Time
	}

fun nextKey [k: Key, ks: set Key]: set Key {
	min [k.ko/nexts & ks]
	}

pred init [t: Time] {
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
	}

pred entry [t, t8: Time, g: Guest, r: Room, k: Key] {
	k in g.keys.t
	let ck = r.currentKey |
		(k = ck.t and ck.t8 = ck.t) or 
		(k = nextKey[ck.t, r.keys] and ck.t8 = k)
	noRoomChangeExcept [t, t8, r]
	noGuestChangeExcept [t, t8, none]
	noFrontDeskChange [t, t8]
	}

pred noFrontDeskChange [t, t8: Time] {
	FrontDesk.lastKey.t = FrontDesk.lastKey.t8
	FrontDesk.occupant.t = FrontDesk.occupant.t8
	}

pred noRoomChangeExcept [t, t8: Time, rs: set Room] {
	all r: Room - rs | r.currentKey.t = r.currentKey.t8
	}
	
pred noGuestChangeExcept [t, t8: Time, gs: set Guest] {
	all g: Guest - gs | g.keys.t = g.keys.t8
	}

pred checkout [t, t8: Time, g: Guest] {
	let occ = FrontDesk.occupant {
		some occ.t.g
		occ.t8 = occ.t - Room ->g
		}
	FrontDesk.lastKey.t = FrontDesk.lastKey.t8
	noRoomChangeExcept [t, t8, none]
	noGuestChangeExcept [t, t8, none]
	}

pred checkin [t, t8: Time, g: Guest, r: Room, k: Key] {
	g.keys.t8 = g.keys.t + k
	let occ = FrontDesk.occupant {
		no occ.t [r]
		occ.t8 = occ.t + r -> g
		}
	let lk = FrontDesk.lastKey {
		lk.t8 = lk.t ++ r -> k
		k = nextKey [lk.t [r], r.keys]
		}
	noRoomChangeExcept [t, t8, none]
	noGuestChangeExcept [t, t8, g]
	}

fact traces {
	init [to/first]
	all t: Time-to/last | let t8 = t.to/next |
		some g: Guest, r: Room, k: Key |
			entry [t, t8, g, r, k]
			or checkin [t, t8, g, r, k]
			or checkout [t, t8, g]
	}

fact NoIntervening {
	all t: Time-to/last | let t8 = t.to/next, t9 = t8.to/next |
		all g: Guest, r: Room, k: Key |
			checkin [t, t8, g, r, k] => (entry [t8, t9, g, r, k] or no t9)
	}

assert NoBadEntry {
	all t: Time, r: Room, g: Guest, k: Key |
		let t8 = t.to/next, o = FrontDesk.occupant.t[r] | 
			entry [t, t8, g, r, k] and some o => g in o
	}

// After adding the NoIntervening fact,
// these commands no longer generate counterexamples
check NoBadEntry for 3 but 2 Room, 2 Guest, 5 Time
check NoBadEntry for 3 but 3 Room, 3 Guest, 7 Time
check NoBadEntry for 5 but 3 Room, 3 Guest, 9 Time
