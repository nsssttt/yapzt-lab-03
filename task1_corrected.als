module task1_corrected

// String fields in the starter model allowed an unconstrained blank value.
// A finite enumeration makes the allowed car models explicit.
abstract sig CarModel {}
one sig Compact, Sedan, SUV extends CarModel {}

sig Person {
    cars: set Car
}

sig Car {
    model: one CarModel
}

fact EveryPersonOwnsACar {
    all p: Person | some p.cars
}

fact NonEmptyExample {
    some Person
    some Car
}

pred drives[p: Person, c: Car] {
    c in p.cars
}

assert EveryCarHasAModel {
    all c: Car | one c.model
}

check EveryCarHasAModel for 3
run {
    some p: Person, c: Car | drives[p, c]
} for 3
