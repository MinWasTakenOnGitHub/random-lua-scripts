math.randomseed(os.time())

local choices = {"sun", "moon", "stars", "cloud"}
local pick = choices[math.random(#choices)]

print("Random pick:", pick)
