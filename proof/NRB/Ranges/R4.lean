import NRB.Sweep

theorem r4_ok : blocks 16384 65536 4294970296 = true := by native_decide

theorem r4 : cover 4294970296 5368712120 := blocks_sound 16384 65536 4294970296 r4_ok
