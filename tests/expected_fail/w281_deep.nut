//expect:w281

function fn(arr) {
  local v = arr ? arr : []
  return v.append(1, 2)
}

return fn

