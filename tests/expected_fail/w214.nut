//expect:w214
local test = ::f

enum REPLAY {
  SKIRMISH = 2
  BATTLE = 3
}

::x <- test ? REPLAY.SKIRMISH : REPLAY.SKIRMISH