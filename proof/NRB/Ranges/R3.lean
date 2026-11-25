import NRB.Sweep

theorem r3_ok : blocks 16384 65536 3221228472 = true := by native_decide

theorem r3 : cover 3221228472 4294970296 := blocks_sound 16384 65536 3221228472 r3_ok
