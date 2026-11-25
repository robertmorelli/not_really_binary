import NRB.Sweep

theorem r12_ok : blocks 16384 65536 12884904888 = true := by native_decide

theorem r12 : cover 12884904888 13958646712 := blocks_sound 16384 65536 12884904888 r12_ok
