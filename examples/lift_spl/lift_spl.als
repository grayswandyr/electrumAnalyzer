open util/ordering[Floor] as fl
open trace[State]

module Lift

sig State {}

fact {infinite}

one sig Lift {
	Open : set State,
	Up : set State,
	current : Floor one -> State,
	load : Load one -> State
} {
 	FEmpty not in Product => Empty not in load.State
	FThird not in Product => Third not in load.State
	FOverload not in Product => Overload not in load.State
}

abstract sig Feature {}
one sig FEmpty, FThird, FOverload, FIdle, FExecutive, FPark extends Feature {}
sig Product in Feature {}

enum Load {Empty, Normal, Third, Overload}

abstract sig Floor {}

abstract sig Button {
  floor : Floor,
  pressed : set State
}

abstract sig LandingButton, LiftButton extends Button {}

abstract sig Event {
  pre,pos : State
}

abstract sig ClosedEvent extends Event {
	bs : set Button
} {
	no bs & pressed.pre
	pre not in Lift.Open
	Lift.load.pre = Lift.load.pos
	pressed.pos = pressed.pre + bs
	Lift.load.pre = Empty => no bs&LiftButton
}

sig Idle extends ClosedEvent { } {
	idle[pre]
	
	FPark in Product => Lift.current.pos = parkLift[pre]
							  else Lift.current.pos = Lift.current.pre

	pos in Lift.Open iff pre in Lift.Open
	pos in Lift.Up iff pre in Lift.Up
}

sig Move extends ClosedEvent { } {
  some LiftCall[pre] + LandingCall[pre]

  Lift.current.pos = moveLift[pre]
  pos in Lift.Open iff willOpen[pos]

  pos in Lift.Up iff pre in Lift.Up
}

sig OpenedEvent extends Event {
	bs : set Button
} {
	no bs & pressed.pre
	no bs & floor.(Lift.current.pre)
	
	pre in Lift.Open
	pos in Lift.Up iff pre in Lift.Up
	current.pos = current.pre
  
	((Overload in Lift.load.pos) || (FIdle in Product && idle[pos])) => pos in Lift.Open else pos not in Lift.Open

--	no floor.(Lift.current.pre) & pressed.pos
	
	let del = Empty in Lift.load.pos => LiftButton else none |
		(pressed.pre-del)-floor.(Lift.current.pre) + bs = pressed.pos
--		(pressed.pre-del)-floor.(Lift.current.pre) in pressed.pos
}

sig ChangeDir extends ClosedEvent {} {
  !idle[pre]
  no LiftCall[pre] + LandingCall[pre]

  not (pos in Lift.Up iff pre in Lift.Up)

  pos in Lift.Open iff pre in Lift.Open
  current.pre = current.pos
}

pred willOpen[s:State] {
  let --filter = (Third = Lift.load.s && some LiftButton&pressed.s) => LiftButton else univ,
       extra = FIdle in Product => idle[s] else some none--,
		--executive = FExecutive in Product => F3 in (pressed.s).floor && F3 not in Lift.current.s else some none 
    | (Lift.current.s in (LiftCall[s] + LandingCall[s]) || extra) 
}

fun moveLift[s:State] : lone Floor {
  Lift.current.s != max[Floor] && s in Lift.Up => next[Lift.current.s] else
  Lift.current.s != min[Floor] && s not in Lift.Up => prev[Lift.current.s] else
  Lift.current.s
}

fun parkLift[s:State] : lone Floor {
    Lift.current.s != min[Floor] => prev[Lift.current.s] else Lift.current.s
}

// the next lift landing button in the current direction
fun LiftCall [s:State] : set Floor {
	(FExecutive in Product && F3 in (pressed.s).floor) => F3&nextFloors[s] else
	calledFloors[s,LiftButton]&nextFloors[s]
}

// the next pressed landing button in the current direction
fun LandingCall [s:State] : set Floor {
	(FExecutive in Product && F3 in (pressed.s).floor) => F3&nextFloors[s] else
	(Third = Lift.load.s && some LiftButton&pressed.s) => none else
	calledFloors[s,LandingButton]&nextFloors[s]
}

// the subset of bs that is currently pressed
fun calledFloors[s : State, bs : set Button] : set Floor {
	(bs&pressed.s).floor
}

// succeeding floors in the current direction
fun nextFloors[s : State] : set Floor {
	(s in Lift.Up) => nextFloorsUp[s]
                          else nextFloorsDown[s]
}

fun nextFloorsUp[s : State] : set Floor {
--  Lift.current.s = last => none else 
(Lift.current.s).*fl/next
}

fun nextFloorsDown[s : State] : set Floor {
--  Lift.current.s = first => none else
 (Lift.current.s).*fl/prev
}

pred idle [s:State] {
  no pressed.s
}

pred init[s:State] {
 Lift.current.s = F1
 s in Lift.Open
 s in Lift.Up
 Lift.load.s = Normal
 no pressed.s
}

fact Trace {
  init[first]
  all s:State | (one e: Event | e.pre = s && e.pos = s.next)
}

// AG (p => AF q)
pred prop1 {
	all s : State | LB3 in pressed.s => some s' : s.future | Lift.current.s' = F3 && s' in Lift.Open
	all s : State | LB2 in pressed.s => some s' : s.future | Lift.current.s' = F2 && s' in Lift.Open
	all s : State | LB1 in pressed.s => some s' : s.future | Lift.current.s' = F1 && s' in Lift.Open
}

// EF (p && EG q)
pred prop1' {
   some s : State | LB2 in pressed.s && all s' : s.future | not (Lift.current.s' = F2 && s' in Lift.Open && s' not in Lift.Up) 
}

// AG (p => AF q)
pred prop2 {
	all s : State | IB3 in pressed.s => some s' : s.future | Lift.current.s' = F3 && s' in Lift.Open  
	all s : State | IB2 in pressed.s => some s' : s.future | Lift.current.s' = F2 && s' in Lift.Open  
	all s : State | IB1 in pressed.s => some s' : s.future | Lift.current.s' = F1 && s' in Lift.Open  
}

// AG (p => A q U r)
pred prop3a {
	all s : State | Lift.current.s = F2 && IB3 in pressed.s && s in Lift.Up =>
		some s' : s.future | Lift.current.s' = F3 && all s'' : upto[s,s'] | s'' in Lift.Up
}

// AG (p => A q U r)
pred prop3b {
	all s : State | Lift.current.s = F3 && IB1 in pressed.s && s not in Lift.Up =>
		some s' : s.future | Lift.current.s' = F1 && all s'' : upto[s,s'] | s'' not in Lift.Up
}

// EF (p && EG q)
pred prop4 {
	some s : State | s not in Lift.Open && all s':s.future | s' not in Lift.Open
}

// EF p
pred prop5a {
  all s : State | not (Lift.current.s = F1 && idle[s] && s not in Lift.Open)
}

// AG (p => EG q) (invalid)
pred prop5b { }

// EF p
pred prop5part { }

// EF p
pred prop5c {
  all s : State | not (Lift.current.s = F2 && idle[s] && s not in Lift.Open)
}

// AG (p => EG q) (invalid)
pred prop5d { }

// EF (p && EG q)
pred prop5e {}

// EF (p && A q U r) (invalid)
pred prop5' {}

// EF p
pred prop6 {
  some s : State | Lift.current.s = F2 && IB2 not in pressed.s && s in Lift.Up && s in Lift.Open
}

// EF p
pred prop7 {
  some s : State | Lift.current.s = F2 && IB2 not in pressed.s && s not in Lift.Up && s in Lift.Open
}

one sig F1 extends Floor { } { this = first }
one sig F2 extends Floor { } { }
one sig F3 extends Floor { } { this = last }
one sig LB1 extends LandingButton { } { floor = F1 }
one sig LB2 extends LandingButton { } { floor = F2 }
one sig LB3 extends LandingButton { } { floor = F3 }
one sig IB1 extends LiftButton { } { floor = F1 }
one sig IB2 extends LiftButton { } { floor = F2 }
one sig IB3 extends LiftButton { } { floor = F3 }

check B1 {no Product => prop1} for 0 but 9 State, 9 Event expect 0
check E1 {Product = FEmpty => prop1} for 0 but 9 State, 9 Event expect 0
check O1 {Product = FOverload => prop1} for 0 but 5 State, 5 Event expect 1
check T1 {Product = FThird => prop1} for 0 but 9 State, 9 Event expect 1
check I1 {Product = FIdle => prop1} for 0 but 9 State, 9 Event expect 0
check X1 {Product = FExecutive => prop1} for 0 but 9 State, 9 Event expect 1
check P1 {Product = FPark => prop1} for 0 but 9 State, 9 Event expect 0
check EO1 {Product = FEmpty + FOverload => prop1} for 0 but 9 State, 9 Event expect 1
check A1 {prop1} for 0 but 9 State, 9 Event expect 1

run B1' {no Product && prop1'} for 0 but 9 State, 9 Event expect 1
run E1' {Product = FEmpty && prop1'} for 0 but 9 State, 9 Event expect 1
run O1' {Product = FOverload && prop1'} for 0 but 9 State, 9 Event expect 1
run T1' {Product = FThird && prop1'} for 0 but 9 State, 9 Event expect 1
run I1' {Product = FIdle && prop1'} for 0 but 9 State, 9 Event expect 1
run X1 {Product = FExecutive && prop1} for 0 but 9 State, 9 Event expect 1
run EO1' {Product = FEmpty + FOverload && prop1'} for 0 but 9 State, 9 Event expect 1
run A1' {prop1'} for 0 but 9 State, 9 Event expect 1
check A1'' {not prop1'} for 0 but 9 State, 9 Event expect 1

check B2 {no Product => prop2} for 0 but 9 State, 9 Event expect 0
check E2 {Product = FEmpty => prop2} for 0 but 9 State, 9 Event expect 1
check O2 {Product = FOverload => prop2} for 0 but 9 State, 9 Event expect 1
check T2 {Product = FThird => prop2} for 0 but 9 State, 9 Event expect 0
check I2 {Product = FIdle => prop2} for 0 but 9 State, 9 Event expect 0
check X2 {Product = FExecutive => prop2} for 0 but 9 State, 9 Event expect 1
check P2 {Product = FPark => prop2} for 0 but 9 State, 9 Event expect 0
check EO2 {Product = FEmpty + FOverload => prop2} for 0 but 9 State, 9 Event expect 1
check A2 {prop2} for 0 but 9 State, 9 Event expect 1

check B3a {no Product => prop3a} for 0 but 9 State, 9 Event expect 0
check E3a {Product = FEmpty => prop3a} for 0 but 9 State, 9 Event expect 1
check O3a {Product = FOverload => prop3a} for 0 but 9 State, 9 Event expect 1
check T3a {Product = FThird => prop3a} for 0 but 9 State, 9 Event expect 1
check I3a {Product = FIdle => prop3a} for 0 but 9 State, 9 Event expect 1
check X3a {Product = FExecutive => prop3a} for 0 but 9 State, 9 Event
check P3a {Product = FPark => prop3a} for 0 but 9 State, 9 Event 
check EO3a {Product = FEmpty + FOverload => prop3a} for 0 but 9 State, 9 Event expect 1
check A3a {prop3a} for 0 but 9 State, 9 Event expect 1

/*check B3b {no Product => prop3b} for 0 but 9 State, 9 Event expect 0
check E3b {Product = FEmpty => prop3b} for 0 but 9 State, 9 Event expect 1
check O3b {Product = FOverload => prop3b} for 0 but 9 State, 9 Event expect 1
check T3b {Product = FThird => prop3b} for 0 but 9 State, 9 Event expect 1
check I3b {Product = FIdle => prop3b} for 0 but 9 State, 9 Event expect 1
check EO3b {Product = FEmpty + FOverload => prop3b} for 0 but 9 State, 9 Event expect 1
check A3b {prop3b} for 0 but 9 State, 9 Event expect 1

run B4 {no Product => prop4} for 0 but 9 State, 9 Event expect 1
run E4 {Product = FEmpty => prop4} for 0 but 9 State, 9 Event expect 1
run O4 {Product = FOverload => prop4} for 0 but 9 State, 9 Event expect 1
run T4 {Product = FThird => prop4} for 0 but 9 State, 9 Event expect 1
run I4 {Product = FIdle => prop4} for 0 but 9 State, 9 Event expect 1
run EO4 {Product = FEmpty + FOverload => prop4} for 0 but 9 State, 9 Event expect 1
run A4 {prop4} for 0 but 9 State, 9 Event expect 1

run B5a {no Product => prop5a} for 0 but 9 State, 9 Event expect 1
run E5a {Product = FEmpty => prop5a} for 0 but 9 State, 9 Event expect 1
run O5a {Product = FOverload => prop5a} for 0 but 9 State, 9 Event expect 1
run T5a {Product = FThird => prop5a} for 0 but 9 State, 9 Event expect 1
run I5a {Product = FIdle => prop5a} for 0 but 9 State, 9 Event expect 1
run EO5a {Product = FEmpty + FOverload => prop5a} for 0 but 9 State, 9 Event expect 1
run A5a {prop5a} for 0 but 9 State, 9 Event expect 1

run B5c {no Product => prop5c} for 0 but 9 State, 9 Event expect 1
run E5c {Product = FEmpty => prop5c} for 0 but 9 State, 9 Event expect 1
run O5c {Product = FOverload => prop5c} for 0 but 9 State, 9 Event expect 1
run T5c {Product = FThird => prop5c} for 0 but 9 State, 9 Event expect 1
run EO5c {Product = FEmpty + FOverload => prop5c} for 0 but 9 State, 9 Event expect 1
run A5c {prop5c} for 0 but 9 State, 9 Event expect 1

run B6 {no Product && prop6} for 0 but 9 State, 9 Event expect 1
run E6 {Product = FEmpty && prop6} for 0 but 9 State, 9 Event expect 1
run O6 {Product = FOverload && prop6} for 0 but 9 State, 9 Event expect 1
run T6 {Product = FThird && prop6} for 0 but 9 State, 9 Event expect 1
run I6 {Product = FIdle && prop6} for 0 but 9 State, 9 Event expect 1
run X6 {Product = FIdle && prop6} for 0 but 9 State, 9 Event expect 1
run P6 {Product = FIdle && prop6} for 0 but 9 State, 9 Event expect 1
run EO6 {Product = FEmpty + FOverload && prop6} for 0 but 9 State, 9 Event expect 1
run A6 {prop6} for 0 but 9 State, 9 Event expect 1

run B7 {no Product && prop7} for 0 but 9 State, 9 Event expect 1
run E7 {Product = FEmpty && prop7} for 0 but 9 State, 9 Event expect 1
run O7 {Product = FOverload && prop7} for 0 but 9 State, 9 Event expect 1
run T7 {Product = FThird && prop7} for 0 but 9 State, 9 Event expect 1
run I7 {Product = FIdle && prop7} for 0 but 9 State, 9 Event expect 1
run X7 {Product = FIdle && prop7} for 0 but 9 State, 9 Event expect 1
run P7 {Product = FIdle && prop7} for 0 but 9 State, 9 Event expect 1
run EO7 {Product = FEmpty + FOverload && prop7} for 0 but 9 State, 9 Event expect 1
run A7 {prop7} for 0 but 9 State, 9 Event expect 1

// #Button = 2x #Floor

run {Product = FPark && some s: State | idle[s] && Lift.current.s = F3 && all s':s.future | idle[s'] } for 0 but 9 State, 9 Event*/
