import NRB.Sweep

theorem r0_ok : blocks 16384 65536 3000 = true := by native_decide

theorem r0 : cover 3000 1073744824 := blocks_sound 16384 65536 3000 r0_ok
