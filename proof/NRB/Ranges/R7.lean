import NRB.Sweep

theorem r7_ok : blocks 16384 65536 7516195768 = true := by native_decide

theorem r7 : cover 7516195768 8589937592 := blocks_sound 16384 65536 7516195768 r7_ok
