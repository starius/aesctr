import AesCtr.Loop
import AesCtr.Bulk.Eor3

namespace AesCtr.Bulk
open AesCtr

/-- Register layout of `ctrBlocksBulkEOR3Asm`: 12 blocks in V0..V11, round keys
ending at V26, plaintext staging V27..V28, the counter in V29, the increments
in V30 and V31. -/
def eor3Layout : Layout := { prog := eor3Program, G := 12, keyEnd := 26, ctr := 29#5, one := 30#5, two := 31#5 }

end AesCtr.Bulk
