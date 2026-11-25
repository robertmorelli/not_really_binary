import NRB.Sweep

theorem r10_ok : blocks 16384 65536 10737421240 = true := by native_decide

theorem r10 : cover 10737421240 11811163064 := blocks_sound 16384 65536 10737421240 r10_ok
