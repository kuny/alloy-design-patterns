
module behavioral/iterator/Collection[E]

sig Collection {
    items: seq E
}

// Collection pred ==============

// Collection.contains(Element e)
pred contains [c: Collection, e: E] {
    some i: c.items.inds | c.items[i] = e
}

// Collection.append(Element e)
pred append [c1, c2: Collection, e: E] {
    // preconditions
    not contains[c1, e]

    // postconditions
    contains[c2, e]
}

// Collection.get(int index)
pred get[c: Collection, i: Int, e: E] {
    // preconditions
    contains[c, e]

    // postconditions
    e = c.items[i]
}

// Collection.seek(Element e)
pred seek[c: Collection, e: E, i: Int] {
    // preconditions
    contains[c, e]

    // postconditions
    e = c.items[i]
}


assert append_after_contains_true {
    all c1, c2: Collection, e: E |
        append[c1, c2, e] => contains[c2, e]
}
check append_after_contains_true for 6