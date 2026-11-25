import NRB.Sweep

theorem r9_ok : blocks 16384 65536 9663679416 = true := by native_decide

theorem r9 : cover 9663679416 10737421240 := blocks_sound 16384 65536 9663679416 r9_ok
