
module behavioral/state/state

enum Mode {
    Standby,
    Running,
    Stopped
}

// 刻々と変化する「現在の状態」
var sig CurrentMode in Mode {}

pred init {
    CurrentMode = Standby
}

// 遷移の定義
pred step {
    CurrentMode = Standby => CurrentMode' = Running
    else CurrentMode = Running => CurrentMode' = Stopped
    else CurrentMode = Stopped => CurrentMode' = Standby
}

fact Traces {
    init
    always step
}

run {} for 6

assert can_return_to_standby {
    always (eventually CurrentMode = Standby)
}
check can_return_to_standby

assert NoIllegalJump {
    always (CurrentMode = Stopped implies CurrentMode' != Running)
}
check NoIllegalJump