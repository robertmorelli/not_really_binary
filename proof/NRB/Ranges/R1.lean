import NRB.Sweep

theorem r1_ok : blocks 16384 65536 1073744824 = true := by native_decide

theorem r1 : cover 1073744824 2147486648 := blocks_sound 16384 65536 1073744824 r1_ok
