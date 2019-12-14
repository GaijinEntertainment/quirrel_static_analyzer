//expect:w240

local a = 2; // can be null
local b = 1;

::print(a ?? b != 1) // expected boolean
