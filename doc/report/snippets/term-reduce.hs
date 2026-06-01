-- snippet from source
reduce (Application ts) =
  case map reduce ts of
    (Abstraction [c] body : arg : t) ->
      reduce $ Application (substitute c arg body : t)
    (Insert 1 : Id : arg : t) ->
      reduce $ Application (Product [arg] : t)
    (Proj i : Product ts : t) ->
      reduce $ Application (ts !! (i - 1) : t)
    (Case cs : Application [Sum i, arg] : t) ->
      reduce $ Application (substitute (varName capture) arg body : t)
    ...
