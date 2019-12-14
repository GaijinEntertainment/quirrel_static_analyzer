//expect:w190
local x
local y
local some_value = 1

function foo() {
  x = some_value

  //here comes long text about how should things work (but they are not)


  (function(){ //-w267
    ::print(1)
  }
  )()

  y = 4
}