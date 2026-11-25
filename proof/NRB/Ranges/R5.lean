import NRB.Sweep

theorem r5_ok : blocks 16384 65536 5368712120 = true := by native_decide

theorem r5 : cover 5368712120 6442453944 := blocks_sound 16384 65536 5368712120 r5_ok
