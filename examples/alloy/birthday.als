module examples/toys/birthday

/*
 * Birthday Book
 *
 * A classic Z example to explain the basic form of an Alloy model. For the original,
 * see J.M. Spivey, The Z Notation, Second Edition, Prentice Hall, 1992.
 *
 * A birthday book has two fields: known, a set of names (of persons whose birthdays are known),
 * and date, a function from known names to dates. The operation AddBirthday adds an association
 * between a name and a date; it uses the relational override operator (++), so any existing
 * mapping from the name to a date is replaced. DelBirthday removes the entry for a given name.
 * FindBirthday obtains the date d for a name n. The argument d is declared to be optional (that is,
 * a singleton or empty set), so if there is no entry for n, d will be empty. Remind gives the set
 * of names whose birthdays fall on a particular day.
 *
 * The assertion AddWorks says that if you add an entry, then look it up, you get back what you
 * just entered. DelIsUndo says that doing DelBirthday after AddBirthday undoes it, as if the add
 * had never happened. The first of these assertions is valid; the second isn8t.
 *
 * The function BusyDay shows a case in which Remind produces more than one card.
 *
 * author: Daniel Jackson, 11/14/01
 */

sig Name {}
sig Date {}
sig BirthdayBook {known: set Name, date: known -> one Date}

pred AddBirthday [bb, bb8: BirthdayBook, n: Name, d: Date] {
    bb8.date = bb.date ++ (n->d)
    }

pred DelBirthday [bb, bb8: BirthdayBook, n: Name] {
    bb8.date = bb.date - (n->Date)
    }

pred FindBirthday [bb: BirthdayBook, n: Name, d: lone Date] {
    d = n.(bb.date)
    }

pred Remind [bb: BirthdayBook, today: Date, cards: set Name] {
    cards = (bb.date).today
    }

pred InitBirthdayBook [bb: BirthdayBook] {
    no bb.known
    }

assert AddWorks {
    all bb, bb8: BirthdayBook, n: Name, d: Date, d8: lone Date |
        AddBirthday [bb,bb8,n,d] && FindBirthday [bb8,n,d8] => d = d8
    }

assert DelIsUndo {
    all bb1,bb2,bb3: BirthdayBook, n: Name, d: Date|
        AddBirthday [bb1,bb2,n,d] && DelBirthday [bb2,bb3,n]
            => bb1.date = bb3.date
    }

check AddWorks for 3 but 2 BirthdayBook expect 0
check DelIsUndo for 3 but 2 BirthdayBook expect 1

pred BusyDay [bb: BirthdayBook, d: Date]{
    some cards: set Name | Remind [bb,d,cards] && !lone cards
    }

run BusyDay for 3 but 1 BirthdayBook expect 1
