import NRB.Sweep

theorem r13_ok : blocks 16384 65536 13958646712 = true := by native_decide

theorem r13 : cover 13958646712 15032388536 := blocks_sound 16384 65536 13958646712 r13_ok
