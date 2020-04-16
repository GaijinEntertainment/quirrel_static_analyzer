//expect:w242

local function x() {
  y()
}

local function y() {
}

return [x, y];