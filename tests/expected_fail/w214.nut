//expect:w214
local test = false

enum REPLAY {
  SKIRMISH = 2
  BATTLE = 3
}

::x <- test ? REPLAY.SKIRMISH : REPLAY.SKIRMISH