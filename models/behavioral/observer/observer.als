module behavioral/observer/observer

sig Observer {}

sig Subject {
    observers: some Observer,
    event: Observer -> lone Int
} 

fact {
    // event のキー（左辺）は、きっちり observers と一致する
    all s: Subject | s.event.Int = s.observers
}

pred notify [s1, s2: Subject] {
    // 購読者リスト自体は変化しない
    s1.observers = s2.observers

    // 通知前 s1: 購読者はみんな 0
    all o: s1.observers | s1.event[o] = 0

    // 通知後 s2: 購読者はみんな 1 に更新される
    all o: s2.observers | s2.event[o] = 1
}

run {} for 6

assert test_notify {
    all s1, s2: Subject |
        notify[s1, s2] => {
            // 購読者リストが同じであることを確認
            s1.observers = s2.observers
            s1.event.Int = s2.event.Int
            // eventが更新されているかnotifyと違う見方で確認
            all e: Observer.(s1.event) | e = 0
            all e: Observer.(s2.event) | e = 1
        }
}

check test_notify for 6