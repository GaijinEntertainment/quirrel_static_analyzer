local arr = [7, 6, 5, null]
local index = 0;

function fn_null() { return null }
function fn_4() { return 4 }
function fn_step() { return arr[index++] }

local x;

if (x := fn_null())
  ::print("fail\n")
else
  ::print("ok\n")


while (x := fn_step())
  ::print(x)
