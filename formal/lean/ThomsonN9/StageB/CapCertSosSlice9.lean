import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSlice9

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_9 : checkKronCapAtT (wForT 9) 9 = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSlice9
