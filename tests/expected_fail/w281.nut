//expect:w281
local x = [1, 2]

function fn(arr) {
  return (arr ?? []).extend(x)
//  ::y <- (arr ?? []).extend(x)
}

return fn

