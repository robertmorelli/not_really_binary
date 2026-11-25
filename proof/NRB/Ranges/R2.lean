import NRB.Sweep

theorem r2_ok : blocks 16384 65536 2147486648 = true := by native_decide

theorem r2 : cover 2147486648 3221228472 := blocks_sound 16384 65536 2147486648 r2_ok
