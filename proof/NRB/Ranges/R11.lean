import NRB.Sweep

theorem r11_ok : blocks 16384 65536 11811163064 = true := by native_decide

theorem r11 : cover 11811163064 12884904888 := blocks_sound 16384 65536 11811163064 r11_ok
