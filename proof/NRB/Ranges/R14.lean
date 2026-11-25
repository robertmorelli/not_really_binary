import NRB.Sweep

theorem r14_ok : blocks 16384 65536 15032388536 = true := by native_decide

theorem r14 : cover 15032388536 16106130360 := blocks_sound 16384 65536 15032388536 r14_ok
