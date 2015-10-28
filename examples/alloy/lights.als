module chapter4/lights ----- The model from page 127

abstract sig Color {}

one sig Red, Yellow, Green extends Color {}

fun colorSequence: Color -> Color {
	(Color <: iden) :> Color + Red->Green + Green->Yellow + Yellow->Red
	}

sig Light {}
sig LightState {color: Light -> one Color}
sig Junction {lights: set Light}

fun redLights [s: LightState]: set Light { s.color.Red }

pred mostlyRed [s: LightState, j: Junction] {
	lone j.lights - redLights[s]
	}

pred trans [s, s8: LightState, j: Junction] {
	lone x: j.lights | x.s.color != x.s8.color
	all x: j.lights |
		let step = x.s.color -> x.s8.color {
			step in colorSequence
			step in Red->(Color-Red) => j.lights in redLights[s]
		}
	}

assert Safe {
	all s, s8: LightState, j: Junction |
		mostlyRed [s, j] and trans [s, s8, j] => mostlyRed [s8, j]
	}

check Safe for 3 but 1 Junction

//assert ColorSequenceDeterministic {
//	all c: Color | lone c.colorSequence
//	}
//
//check ColorSequenceDeterministic
