import NRB.Sweep

theorem r8_ok : blocks 16384 65536 8589937592 = true := by native_decide

theorem r8 : cover 8589937592 9663679416 := blocks_sound 16384 65536 8589937592 r8_ok
