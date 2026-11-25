import NRB.Sweep

theorem r6_ok : blocks 16384 65536 6442453944 = true := by native_decide

theorem r6 : cover 6442453944 7516195768 := blocks_sound 16384 65536 6442453944 r6_ok
