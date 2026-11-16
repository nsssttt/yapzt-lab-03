module library_extended

abstract sig BookStatus {}
one sig Available, Issued extends BookStatus {}

sig User {}
sig Administrator extends User {}

sig Book {}

sig LibraryState {
    status: Book -> one BookStatus,
    borrower: Book -> lone User,
    daysBorrowed: Book -> lone Int
}

fact StateMatchesLoanData {
    all s: LibraryState, b: Book |
        (s.status[b] = Available implies
            no s.borrower[b] and no s.daysBorrowed[b])
        and
        (s.status[b] = Issued implies
            one s.borrower[b] and one s.daysBorrowed[b])
}

fact LoanDuration {
    all s: LibraryState, b: Book |
        s.status[b] = Issued implies
            s.daysBorrowed[b] >= 0 and s.daysBorrowed[b] <= 14
}

fact BorrowingLimit {
    all s: LibraryState, u: User |
        #u.~(s.borrower) <= 3
}

pred borrowAvailableBook[s: LibraryState, u: User, b: Book] {
    s.status[b] = Available
    #u.~(s.borrower) < 3
}

pred administratorReturnsBook[
    priorState, newState: LibraryState,
    admin: Administrator,
    book: Book
] {
    priorState.status[book] = Issued
    newState.status[book] = Available
    no newState.borrower[book]
    no newState.daysBorrowed[book]
    all other: Book - book |
        newState.status[other] = priorState.status[other]
        and newState.borrower[other] = priorState.borrower[other]
        and newState.daysBorrowed[other] = priorState.daysBorrowed[other]
}

assert NoUserBorrowsMoreThanThree {
    all s: LibraryState, u: User |
        #u.~(s.borrower) <= 3
}

assert AvailableBooksHaveNoBorrower {
    all s: LibraryState, b: Book |
        s.status[b] = Available implies no s.borrower[b]
}

run {
    some s: LibraryState, u: User, b: Book |
        borrowAvailableBook[s, u, b]
} for 4 but 5 Int

check NoUserBorrowsMoreThanThree for 4 but 5 Int
check AvailableBooksHaveNoBorrower for 4 but 5 Int

