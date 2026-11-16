module task1_counterexample

sig Person {
    name: one String,
    cars: set Car
}

sig Car {
    model: one String
}

fact EveryPersonOwnsACar {
    all p: Person | some p.cars
}

fact NonEmptyExample {
    some Person
    some Car
}

assert NonBlankModel {
    all c: Car | c.model != " "
}

run {
    some c: Car | c.model = " "
} for 3

check NonBlankModel for 3
