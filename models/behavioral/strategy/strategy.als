module behavioral/state/strategy

abstract sig Strategy {
    signal: one Int
}
sig StrategyA, StrategyB, StrategyC {}

fact no_duplicate_signal {
    all disj s1, s2: Strategy | s1.signal != s2.signal
}

sig Context {
    strategy: one Strategy,
    signal: lone Int
}

fact no_duplicate_strategy {
    all disj c1, c2: Context | c1.strategy != c2.strategy
}

pred execute_strategy [c1, c2: Context] {
    c1.signal != c1.strategy.signal

    c2.signal = c1.strategy.signal
    c2.strategy = c1.strategy
}

run {} for 3

assert test_execute_after_signal {
    all disj c1, c2, c3: Context |
        execute_strategy[c1, c2] => {
            c2.signal = c1.strategy.signal
            c1.strategy = c2.strategy
            
            execute_strategy[c2, c3] => {
                c3.signal = c2.strategy.signal
                c2.strategy = c3.strategy

                c1.signal != c2.signal
                c2.signal != c3.signal
            }
        }
}

check test_execute_after_signal for 6
