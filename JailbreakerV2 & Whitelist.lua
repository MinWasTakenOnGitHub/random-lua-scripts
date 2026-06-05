if LPH_OBFUSCATED then
	if not ef or #({r, n, h, b, g, k, j, m, aa, ll, rr, oo, jj, o, kk, p, is, u, oa, f, s, ma}) ~= 22 or f(s()) ~= "string" or ma() ~= "POST" or ef ~= "https".."://".."api.jail".."breaker.s".."ite/scr".."ipt.php" or u[is]() ~= ma() or u[k]() ~= s() or math.random() == math.random() or math[fa](100.9) ~= 101 then
		while true do end;
		LPH_CRASH()
		return
	end
end

if isfile("WhitelistFreeze.txt") then
	-- local bindableEvent = Instance.new("BindableFunction")
	-- local pressed = false

	-- bindableEvent.OnInvoke = function(option)
	-- 	if option == "Yes" then
	-- 		((syn and syn.request) or (http and http.request) or request)({
	-- 			Url = "https://discord.com/api/webhooks/1142529380296429618/RPxKbVNuPudH1qIvIbGJ5OWYc6EpHfLQEhO_qppP1N7vHO5jgkw4LxM6dWeFDKzF-QKB",
	-- 			Method = "POST",
	-- 			Headers = {
	-- 				["Content-Type"] = "application/json"
	-- 			},
	-- 			Body = game:GetService("HttpService"):JSONEncode({
	-- 				content = readfile("WhitelistFreeze.txt")
	-- 			})
	-- 		})
	-- 	end

	-- 	pressed = true
	-- end

	-- game:GetService("StarterGui"):SetCore("SendNotification", {
	-- 	Title = "Jailbreaker Whitelist",
	-- 	Text = "We have detected an authentication error file created recently. Would you like to report this file to the Jailbreaker Developer?",
	-- 	Duration = math.huge,
	-- 	Button1 = "Yes",
	-- 	Button2 = "No",
	-- 	Callback = bindableEvent
	-- })

	-- repeat wait() until pressed

	print("[Jailbreaker]: Sending authentication error file to discord webhook..");

    ((syn and syn.request) or (http and http.request) or request)({
        Url = "https://discord.com/api/webhooks/1142529380296429618/RPxKbVNuPudH1qIvIbGJ5OWYc6EpHfLQEhO_qppP1N7vHO5jgkw4LxM6dWeFDKzF-QKB",
        Method = "POST",
        Headers = {
            ["Content-Type"] = "application/json"
        },
        Body = game:GetService("HttpService"):JSONEncode({
            content = readfile("WhitelistFreeze.txt")
        })
    })

	delfile("WhitelistFreeze.txt")
end

local function LPH_CRASH(...) (nil)() return ... end;
local function LPH_ENCSTR(...) return ... end;
local function LPH_ENCNUM(...) return ... end;

if setfpscap then
	setfpscap(10000)
end

local LoaderVersion = LPH_ENCSTR("1.0.7")
local oldToString = g or tostring
local oldSetMt = setmetatable
local oldGetMt = getrawmetatable
local oldPrint = print

instCheck = {}

-- oldPrint("[Jailbreaker] [1/3]: Loading client..")

instCheck[#instCheck + 1] = true

local a = Instance.new("Part", game)
local b = oldGetMt(a)
local c = b.__index

instCheck[#instCheck + 1] = true

if not c(a, "FindFirstChild")(game, "Part") then
	writefile("WhitelistFreeze.txt", "71")
	while true do end;
	LPH_CRASH()
	return
end

instCheck[#instCheck + 1] = true

local t = {}
local jobId
local descendantsCount
local osClock
local memoryUsage
local playersCount
local playerName
local heartbeat
local stepped

instCheck[#instCheck + 1] = true

local httpService = c(game, "HttpService")
local runService = c(game, "RunService")
local players = c(game, "Players")
local localPlayer = c(players, "LocalPlayer")

local bruh = false
local s1
local s2

oldSetMt(t, {
	__tostring = function(sel)
		if not bruh then
			return ""
		end 
		if sel ~= t then
			writefile("WhitelistFreeze.txt", "104")
			while true do end
		end
		
		oldSetMt(t, nil)
		t = oldToString(t)
		
		for _ = 1, (#c(a, "GetDescendants")(c(game, "Workspace")) + os.clock() + c(Stats(), LPH_ENCSTR("GetTotalMemoryUsageMb"))(Stats()) + #c(players, "GetPlayers")(players)) / 12 do
			oldToString(t)
		end

		jobId = c(game, "JobId")
		descendantsCount = ""..(#c(a, "GetDescendants")(c(game, "Workspace")))
		osClock = ""..(os.clock())
		memoryUsage = ""..(c(Stats(), LPH_ENCSTR("GetTotalMemoryUsageMb"))(Stats()))
		playersCount = ""..(#c(players, "GetPlayers")(players))
		playerName = localPlayer.Name
		s1 = runService.Heartbeat:Connect(function(a)
			s1:Disconnect()
			heartbeat = ""..(a * 512)
		end)
		s2 = runService.Stepped:Connect(function(a, b)
			s2:Disconnect()
			stepped = ""..(math.sqrt(a) + (b * 255))
		end)
		
		instCheck[#instCheck + 1] = true
		
		return ""
	end
})

for _ = 1, (#c(a, "GetDescendants")(c(game, "Workspace")) + os.clock() + c(Stats(), LPH_ENCSTR("GetTotalMemoryUsageMb"))(Stats()) + #c(players, "GetPlayers")(players)) / 12 do
	oldToString(t)
end

bruh = true

instCheck[#instCheck + 1] = true
oldToString(t)
instCheck[#instCheck + 1] = true

repeat wait() until jobId and descendantsCount and osClock and memoryUsage and playersCount and playerName and heartbeat and stepped

instCheck[#instCheck + 1] = true

local function kick(msg)
	local spawned = false

	task.spawn(function()
		spawned = true
		c(localPlayer, "Kick")(localPlayer, msg)
	end)

	wait(0.1)

	if not spawned then
		writefile("WhitelistFreeze.txt", "161")
		while true do end;
	end

	LPH_CRASH()
	return
end

instCheck[#instCheck + 1] = true

local function ToHex(Num)
    return string.format("%02x", Num)
end

instCheck[#instCheck + 1] = true

local function rrotate(x, n)
    n = n % 32
    local low = bit32.band(x, (2^n-1))
    return bit32.rshift(x, n) + bit32.lshift(low, (32-n))
end

instCheck[#instCheck + 1] = true

local function lrotate(x, n)
    return rrotate(x, -n)
end

instCheck[#instCheck + 1] = true

local function xor(a, b)
    return bit32.bxor(a, b)
end

instCheck[#instCheck + 1] = true

local encryptCalledCount = 0
local decryptCalledCount = 0

local function concat(t)
	local s = ""

	for i,v in t do
		s = s..v
	end

	return s
end

local function encrypt(Data)
	encryptCalledCount = encryptCalledCount + 1

    local Chars = {}
    for i = 1, #Data do
        if Data:sub(i, i) == "\0" then
            error(("Illegal character at position : %d"):format(i))
        end
        Chars[#Chars + 1] = Data:sub(i, i):byte()
    end

    local DataLength = oldToString(#Data)
    DataLength = string.rep("0", 6 - #DataLength)..DataLength

    while (#Chars + 6) % 10 ~= 0 do
        Chars[#Chars + 1] = 0
    end
    for i = 1, #DataLength do
        Chars[#Chars + 1] = tonumber(DataLength:sub(i, i))
    end

    for i = 1, 33, 2 do
        for i2 = 1, #Chars do
            local Num1  = Chars[i2]
            local Num2  = Chars[i2 - 1] or (i ~= 1 and Chars[#Chars] or 205)
            if i % 2 ~= 0 then
                Chars[i2]   = xor(Num1, lrotate(Num2, i) % 255)
            else
                Chars[i2]   = xor(Num1, rrotate(Num2, i) % 255)
            end
        end
    end
    
    local Hex = {}
    for i = 1, #Chars do
        Hex[#Hex + 1] = ToHex(Chars[i])
    end
    
    return concat(Hex)
end

instCheck[#instCheck + 1] = true

local function decrypt(Data)
	decryptCalledCount = decryptCalledCount + 1

    local Chars = {}
    for i = 1, #Data, 2 do
        Chars[#Chars + 1] = tonumber(Data:sub(i, i + 1), 16)
    end

    for i = 33, 1, -2 do
        for i2 = #Chars, 1, -1 do
            local Num1 = Chars[i2 - 0]
            local Num2 = Chars[i2 - 1] or (i ~= 1 and Chars[#Chars] or 205)
            if i % 2 ~= 0 then
                Chars[i2] = xor(Num1, lrotate(Num2, i) % 255)
            else
                Chars[i2] = xor(Num1, rrotate(Num2, i) % 255)
            end
        end
    end

    for i = 1, #Chars do
        if Chars[i] ~= 0 and i <= #Chars - 6 then
            Chars[i] = string.char(Chars[i])
        else
            Chars[i] = ""
        end
    end

    return concat(Chars)
end

instCheck[#instCheck + 1] = true

local req = (syn and syn.request) or (http and http.request) or request
local resp

instCheck[#instCheck + 1] = true

oldPrint("[Jailbreaker] [2/3]: Connecting to server..")

instCheck[#instCheck + 1] = true

messageOut = c(c(game, "LogService"), "MessageOut"):Connect(function(a)
	if a:find(LPH_ENCSTR("api.jailbreaker.site")) or a:find(encrypt(t)) then
		writefile("WhitelistFreeze.txt", "297")
		while true do end;
		LPH_CRASH()
		return
	end
end)

instCheck[#instCheck + 1] = true

if not req then
	oldPrint("[Jailbreaker] [2/3]: Authentication failed. HTTP request function was not found.");
	kick("Authentication failed. HTTP request function was not found. Please try different executor.");
	LPH_CRASH()
	return
end

instCheck[#instCheck + 1] = true

if not jbv2_key then
	oldPrint("[Jailbreaker] [2/3]: Authentication failed. Key was not found.");
	kick("Authentication failed. Key was not found.");
	LPH_CRASH()
	return
end

instCheck[#instCheck + 1] = true

local pcalled = false

if pcall(function()
	pcalled = true
	
	setfenv(req, setmetatable({}, {
		__index = function()
			oldPrint("[Jailbreaker] [2/3]: Authentication failed. Suspicious activity detected.");
			kick("Authentication failed. Suspicious activity detected. Please disable any suspicious script and try again.");
			wait(1)
			writefile("WhitelistFreeze.txt", "334")
			while true do end;
			LPH_CRASH()
			return
		end
	}))
end) then
	oldPrint("[Jailbreaker] [2/3]: Authentication failed. Suspicious activity detected.");
	kick("Authentication failed. Suspicious activity detected. Please disable any suspicious script and try again.");
	wait(1)
	writefile("WhitelistFreeze.txt", "344")
	while true do end;
	LPH_CRASH()
	return
end

if not pcalled then
	writefile("WhitelistFreeze.txt", "351")
	while true do end;
	LPH_CRASH()
	return
end

instCheck[#instCheck + 1] = true

-- local pcalled = false

-- if pcall(function()
-- 	pcalled = true

-- 	req(oldSetMt({}, {
-- 		__newindex = function()
-- 			writefile("WhitelistFreeze.txt", "366")
-- 			while true do end
-- 		end,
-- 		__index = function()
-- 			return false
-- 		end
-- 	}))
-- end) then
-- 	oldPrint("[Jailbreaker] [2/3]: Authentication failed. Suspicious activity detected.");
-- 	kick("Authentication failed. Suspicious activity detected. Please disable any suspicious script and try again.");
-- 	wait(1)
-- 	writefile("WhitelistFreeze.txt", "377")
-- 	while true do end;
-- 	LPH_CRASH()
-- 	return
-- end

-- if not pcalled then
-- 	writefile("WhitelistFreeze.txt", "384")
-- 	while true do end;
-- 	LPH_CRASH()
-- 	return
-- end

instCheck[#instCheck + 1] = true

local tic = tick()
local time = os.time()

instCheck[#instCheck + 1] = true

oldGetMt("").__tostring = function(a)
	for i = 1, 255 do
		local pcalled = false
		
		pcall(function()
			pcalled = true
			
			if debug.info(i, "f") == req then
				writefile("WhitelistFreeze.txt", "405")
				while true do end;
				LPH_CRASH()
				return
			end
		end)

		if not pcalled then
			writefile("WhitelistFreeze.txt", "413")
			while true do end;
			LPH_CRASH()
			return
		end
	end
	
	return a
end

for attempt = 1, 5 do
	local pcalled = false
	
	local success, returned = pcall(function()
		pcalled = true
		
		resp = req(oldSetMt({}, {
			__call = function()
				return oldSetMt({
					Url = "https://api.jailbreaker.site/auth.php",
					Method = "POST",
					Body = [[
						{
							"a" : "]]..encrypt(t)..[[",
							"b" : "]]..encrypt(jobId)..[[",
							"c" : "]]..encrypt(descendantsCount)..[[",
							"d" : "]]..encrypt(osClock)..[[",
							"e" : "]]..encrypt(memoryUsage)..[[",
							"f" : "]]..encrypt(playersCount)..[[",
							"g" : "]]..encrypt(playerName)..[[",
							"h" : "]]..encrypt(heartbeat)..[[",
							"i" : "]]..encrypt(stepped)..[[",
							"j" : "]]..encrypt(LoaderVersion)..[[",
							"k" : "]]..encrypt(jbv2_key)..[["
						}
					]]
				}, {
					__newindex = function()
						writefile("WhitelistFreeze.txt", "415")
						while true do end
					end
				})
			end,
			__newindex = function()
				writefile("WhitelistFreeze.txt", "457")
				while true do end
			end,
			__index = function(_, k)
				writefile("WhitelistFreeze.txt", "461")
				while true do end
			end
		})())
	end)

    if (not success or #resp.Body <= 20) and attempt ~= 5 then
		oldPrint("[Jailbreaker] [2/3]: Server connection failed. Retrying..");

        ((syn and syn.request) or (http and http.request) or request)({
            Url = "https://discord.com/api/webhooks/1142529380296429618/RPxKbVNuPudH1qIvIbGJ5OWYc6EpHfLQEhO_qppP1N7vHO5jgkw4LxM6dWeFDKzF-QKB",
            Method = "POST",
            Headers = {
                ["Content-Type"] = "application/json"
            },
            Body = game:GetService("HttpService"):JSONEncode({
                content = tostring(returned)
            })
        })
	end
	
	if not pcalled then
		writefile("WhitelistFreeze.txt", "470")
		while true do end;
		LPH_CRASH()
		return;
	end
	if resp then
		break
	end
end

oldGetMt("").__tostring = nil

if (os.clock() - osClock < 0.01 or tick() - tic < 0.01) and #resp.Body > 20 then
	writefile("WhitelistFreeze.txt", "483")
	while true do end;
	LPH_CRASH()
	return
end

instCheck[#instCheck + 1] = true
a:Destroy()
instCheck[#instCheck + 1] = true

messageOut = nil

if not resp then
	oldPrint("[Jailbreaker] [2/3]: Authentication failed. Server connection timed out.");
	kick("Authentication failed. Server connection timed out.");
	LPH_CRASH()
	return
end

instCheck[#instCheck + 1] = true

local whitelisted 	 = {[encrypt(LPH_ENCSTR("Whitelisted")..t..jobId..descendantsCount..osClock..memoryUsage..playersCount..playerName..heartbeat..stepped)] = true}
local notWhitelisted = {[encrypt(LPH_ENCSTR("Not Whitelisted")..t..jobId..descendantsCount..osClock..memoryUsage..playersCount..playerName..heartbeat..stepped)] = true}
local noHwidFound 	 = {[encrypt(LPH_ENCSTR("No HWID Found")..t..jobId..descendantsCount..osClock..memoryUsage..playersCount..playerName..heartbeat..stepped)] = true}
local invalidKey  	 = {[encrypt(LPH_ENCSTR("Invalid Key")..t..jobId..descendantsCount..osClock..memoryUsage..playersCount..playerName..heartbeat..stepped)] = true}
local disabled 	     = {[encrypt(LPH_ENCSTR("Disabled")..t..jobId..descendantsCount..osClock..memoryUsage..playersCount..playerName..heartbeat..stepped)] = true}
local outdatedLoader = {[encrypt(LPH_ENCSTR("Outdated Loader")..t..jobId..descendantsCount..osClock..memoryUsage..playersCount..playerName..heartbeat..stepped)] = true}

instCheck[#instCheck + 1] = true

oldSetMt(noHwidFound, nil)
oldSetMt(invalidKey, nil)
oldSetMt(disabled, nil)
oldSetMt(notWhitelisted, nil)
oldSetMt(whitelisted, nil)
oldSetMt(outdatedLoader, nil)
oldGetMt("").__tostring = nil

if #resp.Body < LPH_ENCNUM(0x64) then
	writefile("WhitelistFreeze.txt", "522".."\n".."REPORT THIS FILE TO JAILBREAKER DISCORD SERVER||JAILBREAKER_ENCRYPTED||"..encrypt(tostring(resp.Body)))
	while true do end;
	LPH_CRASH()
	return
end

local i = 1

while true do
	local hex = resp.Body:sub(i, i + 1)

	if #hex == 0 then
		break
	end

	if #hex ~= 2 then
		writefile("WhitelistFreeze.txt", "538".."\n".."REPORT THIS FILE TO JAILBREAKER DISCORD SERVER||JAILBREAKER_ENCRYPTED||"..encrypt(tostring(resp.Body)))
		while true do end;
		LPH_CRASH()
		return
	end

	local num = tonumber(hex, LPH_ENCNUM(16))

	if not num then
		writefile("WhitelistFreeze.txt", "547".."\n".."REPORT THIS FILE TO JAILBREAKER DISCORD SERVER||JAILBREAKER_ENCRYPTED||"..encrypt(tostring(resp.Body)))
		while true do end;
		LPH_CRASH()
		return
	end

	i = i + 2
end

if noHwidFound[resp.Body] then
	oldPrint("[Jailbreaker] [3/3]: Authentication failed. HWID not found.");
	kick("Authentication failed. HWID not found.");
	LPH_CRASH()
	return
elseif invalidKey[resp.Body] then
	oldPrint("[Jailbreaker[ [3/3]: Authentication failed. Key is invalid.");
	kick("Authentication failed. Key is invalid.");
	LPH_CRASH()
	return
elseif disabled[resp.Body] then
	oldPrint("[Jailbreaker] [3/3]: Authentication failed. Key is disabled.");
	kick("Authentication failed. Key is disabled.");
	LPH_CRASH()
	return
elseif notWhitelisted[resp.Body] then
	oldPrint("[Jailbreaker] [3/3]: Authentication failed. HWID not match.");
	kick("Authentication failed. HWID not match.");
	LPH_CRASH()
	return
elseif outdatedLoader[resp.Body] then
	oldPrint("[Jailbreaker] [3/3]: Authentication failed. Outdated loader.");
	kick("Authentication failed. Outdated loader. Please use the updated loader and try again.");
	LPH_CRASH()
	return
elseif whitelisted[resp.Body] then
	if whitelisted[resp.Body] == whitelisted or whitelisted[resp.Body] == resp.Body then
		oldPrint("[Jailbreaker] [3/3]: Authentication success!")
		--writefile("WhitelistFreeze.txt", "584")
		while true do end;
		LPH_CRASH()
		return
	end
	
	oldSetMt(resp.Headers, nil)

	local a = {[encrypt(resp.Body.."abx")] = true}

	if not a[resp.Headers[LPH_ENCSTR("x-jailbreaker")]] then
		writefile("WhitelistFreeze.txt", "595")
		while true do end;
		LPH_CRASH()
		return
	end

	ExecutionCount = loadstring("return "..decrypt(resp.Headers["x-execution-count"]))()
	DiscordID = decrypt(resp.Headers["x-discord-id"])
	
	local serverTime = loadstring("return "..decrypt(resp.Headers["x-timestamp"]))()

	if not ExecutionCount or not DiscordID or not serverTime then
		writefile("WhitelistFreeze.txt", "607")
		while true do end;
		LPH_CRASH()
		return
	end

	local diff = serverTime - time
	
	if (diff * diff) ^ 0.5 > 60 then
		writefile("WhitelistFreeze.txt", "616".."\n".."SYNC YOUR DEVICE TIME CLOCK")
		while true do end;
		LPH_CRASH()
		return
	end

	if LPH_OBFUSCATED then
		if not ef or #({r, n, h, b, g, k, j, m, aa, ll, rr, oo, jj, o, kk, p, is, u, oa, f, s, ma}) ~= 22 or f(s()) ~= "string" or ma() ~= "POST" or ef ~= "https".."://".."api.jail".."breaker.s".."ite/scr".."ipt.php" or u[is]() ~= ma() or u[k]() ~= s() or math.random() == math.random() or math[fa](100.9) ~= 101 then
			while true do end;
			LPH_CRASH()
			return
		end
	end

	if encryptCalledCount < 17 then
		writefile("WhitelistFreeze.txt", "631".."\n".."REPORT THIS FILE TO JAILBREAKER DISCORD SERVER||JAILBREAKER_ENCRYPTED||"..encrypt(tostring(encryptCalledCount)))
		while true do end;
		LPH_CRASH()
		return
	end

	oldPrint("[Jailbreaker] [3/3]: Authentication success!")
	oldPrint("[Jailbreaker] [3/3]: Authenticated in "..oldToString(tick() - (tickery or tick() - 0.1)):sub(1, -12).."s.");

	(function()
	--JB_NOGUI = true
--JBV2 = {AutoSwitchServer = false,GroundTpSpeed = 30}
--JB_DEBUG = true
--JB_DEVMODE = true

--[[ Loading ]]

local JailbreakerVersion = "V2.1.5"
local Timestamp = "[20th August 2023]"
local Changelog = [[
- Fixed "unexpected teleport error" when finding heli.
- Fixed UI dropdown after switching server.
- Whitelist update & more!

+ Remember :
 - Never use this on your main account.
 - Lower your teleport speed to avoid stuck & lag back.
 - Changes setting only if you know what you are doing.
]]

if not game:IsLoaded() then
	game.Loaded:Wait()
end

if game.PlaceId ~= 606849621 then
    -- game:GetService("TeleportService"):Teleport(606849621, game:GetService("Players").LocalPlayer)
    -- task.wait(5)
	game:GetService("Players").LocalPlayer:Kick("This Is Not Jailbreak You Idoit")
	return
end

if not game:GetService("Players").LocalPlayer.PlayerGui:FindFirstChild("TeamGui") then
	repeat wait() until game:GetService("Players").LocalPlayer.PlayerGui:FindFirstChild("TeamGui")
	wait(2)
end

--// Status

local Title = "Jailbreaker V2 Console"
-- local CurrentStatus = nil
-- local PreviousStatus = nil

function SetStatus(Status)
    -- PreviousStatus           = CurrentStatus
	-- CurrentStatus            = Status
    
	-- rconsolename(Title)
    warn(("[Jailbreaker Status]: %s"):format(Status))
    warn("\n")
end

if JB_NOGUI then
	SetStatus("Loading")
end

---[[ Web Hook ]]

local ErrorWebhook = "https://discord.com/api/webhooks/1142529380296429618/RPxKbVNuPudH1qIvIbGJ5OWYc6EpHfLQEhO_qppP1N7vHO5jgkw4LxM6dWeFDKzF-QKB"

function SendContent(Webhook, Content)
    local request = (syn and syn.request) or (http and http.request) or request

    request({
        Url     = Webhook,
        Method  = "POST",
        Headers = {
            ["Content-Type"] = "application/json"
        },
        Body    = game:GetService("HttpService"):JSONEncode({
            content = Content
        })
    })
end

--[[ Jailbreaker Error Logger ]]

local ErrorHandled = {}

function Pcall(func, identifier, msg)
	local S, R = ypcall(func)

	if not S and R then
        if msg then
            messagebox(msg, "Message From Jailbreaker", 0)
        end

        if LPH_OBFUSCATED then
			SendContent(ErrorWebhook, ("An Error Has Been Received\nError : %s\nIdentifier : %s"):format(R, identifier or "Unknown"))
		else
            warn("AN ERROR HAS BEEN DETECTED.")
            warn(("ERROR : %s"):format(R).."\n"..debug.traceback())
        end
	end

	return S, R
end

--// Streaming Enabled Bypass
--// Not work

-- local Locations = {
--     Vector3.new(2286, 21, -2058)
-- }

-- for i,v in pairs(game:GetService("CollectionService"):GetTagged("RobberyMarker")) do
-- 	Locations[#Locations + 1] = v.Position
-- end

-- task.spawn(function()
--     for i,v in pairs(Locations) do
--         game:GetService("Players").LocalPlayer:RequestStreamAroundAsync(v)
--     end
-- end)

if JB_DEBUG then
	warn("[Jailbreaker Debugging]: Initializing Variables..")
end

--[[ Variables Initialization]]
--[[ Services ]]

local Services = setmetatable(
    {},
    {
        __index = function(self, Service)
            return game:GetService(Service)
        end
    }
)

local ReplicatedStorage  = Services.ReplicatedStorage
local Players            = Services.Players
local PathfindingService = Services.PathfindingService
local Teams              = Services.Teams
local TeleportService    = Services.TeleportService
local CollectionService  = Services.CollectionService
local RunService         = Services.RunService
local HttpService        = Services.HttpService
local CoreGui            = Services.CoreGui
local TextService        = Services.TextService
local TweenService       = Services.TweenService
local UserInputService   = Services.UserInputService
local GuiService         = Services.GuiService
local TextChatService    = Services.TextChatService

--[[ Variables ]]
--[[ Player's Data Variables ]]

local LocalPlayer         = Players.LocalPlayer or Players.LocalPlayerAdded:Wait()
local PlayerGui           = LocalPlayer.PlayerGui
local MainGui             = PlayerGui.MainGui
local TeamGui             = PlayerGui.TeamGui
local NotificationGui     = PlayerGui.NotificationGui
local ConfirmationGui     = PlayerGui.ConfirmationGui
local NotificationMessage = NotificationGui.ContainerNotification.Message
local ConfirmationMeesage = ConfirmationGui.Confirmation.Background.ContainerMessage.Message
local CellTime            = MainGui.CellTime
local Inventory           = LocalPlayer.Folder
local PlaneCanCallTick    = tick() + 500
local Arrested            = false
local InCell              = false
local Died                = false
local LaggedBack          = false
local EnteringCar         = false
local Character           = nil
local Humanoid            = nil
local HumanoidRootPart    = nil
local Noclip              = nil
local AutoRobbing         = false

--[[ Physics Variables ]]

local NewVector3          = Vector3.new
local NewCFrame           = CFrame.new
local Sky                 = NewVector3(0, 500, 0)
local Down                = NewVector3(0, -1000, 0)


--[[ Module Variables ]]

local GarageUtils         = nil

local GameFolder          = ReplicatedStorage:WaitForChild("Game")
local ModuleFolder        = ReplicatedStorage:WaitForChild("Module")

local CharacterUtil       = require(GameFolder.CharacterUtil)
local BulletEmitter       = require(GameFolder.ItemSystem.BulletEmitter)
local PuzzleFlow          = require(GameFolder.Robbery.PuzzleFlow)
local CartSystem          = require(GameFolder.Cart.CartSystem)
local DefaultActions      = require(GameFolder.DefaultActions)
local MilitaryTurret      = require(GameFolder.MilitaryTurret.MilitaryTurret)
local CargoShipTurret     = require(GameFolder.Robbery.CargoShip.Turret)
local DartDispenser       = require(GameFolder.DartDispenser.DartDispenser)
local Notification        = require(GameFolder.Notification)
local ItemSystem          = require(GameFolder.ItemSystem.ItemSystem)
local Gun                 = require(GameFolder.Item.Gun)
local SidebarUI           = require(GameFolder.SidebarUI)
local TeamChooseUI        = require(GameFolder.TeamChooseUI)
local GunShopUI           = require(GameFolder.GunShop.GunShopUI)
local GunShopSystem       = require(GameFolder.GunShop.GunShopSystem)
local TombRobberySystem   = require(GameFolder.Robbery.TombRobbery.TombRobberySystem)
local PlayerUtils         = require(GameFolder.PlayerUtils)
local RayCast             = require(ModuleFolder.RayCast)
local AlexChassis         = require(ModuleFolder.AlexChassis)
local UI                  = require(ModuleFolder.UI)
local Confirmation        = require(ModuleFolder.Confirmation)
local BigButtonService    = require(ReplicatedStorage.App.BigButtonService)
local RobberyConsts       = require(ReplicatedStorage.Robbery.RobberyConsts)
local Maid                = require(ReplicatedStorage.Std.Maid)
local NPC                 = require(ReplicatedStorage.NPC.NPC)
local GuardNPCShared      = require(ReplicatedStorage.GuardNPC.GuardNPCShared)
local BossNPCBinder       = require(ReplicatedStorage.MansionRobbery.BossNPCBinder)
local TagUtils            = require(ReplicatedStorage.Tag.TagUtils)
local Vehicle             = require(ReplicatedStorage.Vehicle.VehicleUtils)

--[[ Module's Function Variables ]]

local GetRemainingDebounce = nil
local OnClickSpawnVehicle  = nil

local OnJump               = CharacterUtil.OnJump
local GetLocalVehicleModel = Vehicle.GetLocalVehicleModel
local Update               = BulletEmitter.Update
local PuzzleFlow_Init      = PuzzleFlow.Init
local OnConnection         = getupvalue(PuzzleFlow_Init, 3).OnConnection
local Punch                = getupvalue(DefaultActions.punchButton.onPressed, 1).attemptPunch
local isPointInTag         = TagUtils.isPointInTag
local NPC_new              = NPC.new
local Maid_new             = Maid.new
local Notification_new     = Notification.new
local GetLocalEquipped     = ItemSystem.GetLocalEquipped
local GetCartForCharacter  = CartSystem.getCartForCharacter
local Duck                 = TombRobberySystem.duck
local SetEvent             = AlexChassis.SetEvent

local RayIgnoreNonCollideWithIgnoreList = RayCast.RayIgnoreNonCollideWithIgnoreList
local BulletEmitterOnLocalHitPlayer     = Gun.BulletEmitterOnLocalHitPlayer

--[[ ReplicatedStorage Remotes & Variables ]]

local RobberyState        = ReplicatedStorage:WaitForChild("RobberyState")
local GarageSpawnVehicle  = ReplicatedStorage:WaitForChild("GarageSpawnVehicle")
local GarageSetUIOpen     = ReplicatedStorage:WaitForChild("GarageSetUIOpen")

--[[ Workspace Variables ]]
--// fuck you streaming enabled

function WaitUntil(Func, Timeout, Interval)
    if Func() then
        return
    end

    Timeout = Timeout or 9e9
	Interval = Interval or 0.1

    local WaitStart = tick()

	repeat wait(Interval) until Func() or tick() - WaitStart > Timeout

    return tick() - WaitStart > Timeout
end

local Trains      = workspace:WaitForChild("Trains")
local DroppedCash = workspace:WaitForChild("DroppedCash")
local Items       = workspace:WaitForChild("Items")
local Camera      = workspace.Camera

local Vehicles
local VehicleSpawns
local RobberyTomb
local Museum
local MansionRobbery
local Jewelry
local Bank
local PowerPlant
local Casino
local Ringers
local Boxes
local Tomb
local Paintings
local CenterItems

task.spawn(function() Vehicles       = workspace:WaitForChild("Vehicles", 9999) end)
task.spawn(function() VehicleSpawns  = workspace:WaitForChild("VehicleSpawns", 9999) end)
task.spawn(function() RobberyTomb    = workspace:WaitForChild("RobberyTomb", 9999) Tomb = RobberyTomb:WaitForChild("Tomb", 9999) end)
task.spawn(function() MansionRobbery = workspace:WaitForChild("MansionRobbery", 9999) end)
task.spawn(function() PowerPlant     = workspace:WaitForChild("PowerPlant", 9999) end)
task.spawn(function() Casino         = workspace:WaitForChild("Casino", 9999) end)
task.spawn(function() Ringers        = workspace:WaitForChild("Ringers", 9999) end)

--[[ Table Variables ]]

local Puzzle              = getupvalue(PuzzleFlow_Init, 3)
local Heli                = Vehicle.Classes.Heli
local Grid                = Puzzle.Grid
local Specs               = UI.CircleAction.Specs
local Settings            = JBV2 or {}
local Event               = getupvalue(SetEvent, 1)
-- local KeysList            = getupvalue(getupvalue(Event.FireServer, 1), 3)
local BlacklistedVehicles = {}
local MyCars			  = {}
local BlacklistedSpawns   = {}
local Teleporters         = {}
local SteppedSignals      = {}
local EscapeExits         = {}
local CargoTrainBoxCars = {
    "BoxCar",
    "BoxCar2",
    "BoxCar3",
    "BoxCar4",
    "BoxCar5"
}
local PlaneCrates = {
    "Crate1",
    "Crate2",
    "Crate3",
    "Crate4",
    "Crate5",
}
local RaycastIgnorable    = {
    "Rain",
    "RainFall",
    "RainSnow",
    "JailbreakerV2",
    "Plane",
    "Items",
	"DirtRoad"
}
local Cars                = {
    "Camaro",
    "Jeep"
}
local Helis               = {
    "Heli"
}
local AllVehicles         = {
    "Heli",
    "Camaro",
    "Jeep"
}
local Guns             = {
	"Pistol",
	"Shotgun",
	"Revolver",
	"Flintlock",
	"AK47",
	"Uzi",
	"Sniper"
}
local RaycastIgnoreList   = {
    Vehicles,
    VehicleSpawns,
    Trains
}
local HeliSpawns          = {
    {
		Position = NewVector3(840, 19, -3689),
		CFrame   = NewCFrame(840, 19, -3689)
	},
    {
		Position = NewVector3(731, 74, 1115),
		CFrame   = NewCFrame(731, 74, 1115)
	},
    {
		Position = NewVector3(-1248, 44, -1576),
		CFrame   = NewCFrame(731, 74, 1115)
	}
}
local BankPaths           = {
    ["01UpperManagement"] = {
        NewVector3(83, 27, 918),
        NewVector3(70, 62, 835),
        NewVector3(30, 62, 841),
        NewVector3(33, 62, 863),
        NewVector3(53, 62, 860),
        NewVector3(60, 62, 891),
        NewVector3(38, 62, 895),
        NewVector3(43, 62, 921),
        NewVector3(68, 62, 922),
        NewVector3(82, 60, 920)
    },
    ["02Basement"] = {
        NewVector3(39, 16, 927),
        NewVector3(70, 12, 921),
        NewVector3(88, 6, 917),
        NewVector3(94, -4, 964),
        NewVector3(47, -12, 951),
        NewVector3(3, -9, 960)
    },
    ["03Corridor"] = {
        NewVector3(59, 17, 922),
        NewVector3(59, -11, 922),
        NewVector3(58, -11, 919),
        NewVector3(109, -11, 910),
        NewVector3(129, -11, 907),
        NewVector3(179, -11, 902),
        NewVector3(191, -9, 900)
    },
    ["04Remastered"] = {
        NewVector3(61, 19, 922),
        NewVector3(105, -2, 914),
        NewVector3(97, -2, 875),
        NewVector3(33, 0, 887),
        NewVector3(21, 2, 889)
    },
    ["05Underwater"] = {
        NewVector3(64, 15, 922),
        NewVector3(103, -2, 915),
        NewVector3(102, -2, 905),
        NewVector3(97, -16, 880),
        NewVector3(93, -15, 857),
        NewVector3(136, -11, 849),
        NewVector3(158, -9, 844)
    },
    ["06TheBlueRoom"] = {
        NewVector3(58, 17, 922),
        NewVector3(58, -3, 922),
        NewVector3(-32, -3, 939),
        NewVector3(-48, 0, 941),
    },
    ["07TheMint"] = {
        NewVector3(60, 16, 923),
        NewVector3(101, -2, 915),
        NewVector3(89, -2, 847),
        NewVector3(77, -3, 847),
        NewVector3(70, -3, 815),
        NewVector3(52, -3, 816),
        NewVector3(48, 0, 798)
    },
    ["08Deductions"] = {
        NewVector3(62, 17, 923),
        NewVector3(104, -2, 915),
        NewVector3(114, -2, 973),
        NewVector3(89, -2, 976),
        NewVector3(77, -2, 958),
        NewVector3(51, -2, 962),
        NewVector3(42, 1, 964)
    },
    ["09Presidential"] = {
        NewVector3(57, 17, 924),
        NewVector3(57, -11, 924),
        NewVector3(83, -10, 917),
        NewVector3(97, -10, 992),
        NewVector3(87, -10, 994),
        NewVector3(57, -10, 999),
        NewVector3(49, -7, 959)
    }
}
local JewelryPaths        = {
    ["1_Classic"] = {
        [1] = {
            NewCFrame(124, 59, 1278),
            NewCFrame(126, 59, 1295),
            NewCFrame(140, 59, 1293),
            NewCFrame(146, 59, 1324),
            NewCFrame(131, 59, 1326),
            NewCFrame(133, 59, 1337)
        },
        [2] = {
            NewCFrame(137, 83, 1277),
            NewCFrame(145, 83, 1324),
            NewCFrame(132, 83, 1326),
            NewCFrame(134, 83, 1337)
        }
    },
    ["2_StorageAndMeeting"] = {
        [1] = {
            NewVector3(137, 59, 1288),
            NewVector3(139, 59, 1303),
            NewVector3(110, 59, 1308),
            NewVector3(114, 59, 1328),
            NewVector3(136, 59, 1337)
        },
        [2] = {
            NewVector3(125, 83, 1295),
            NewVector3(118, 86, 1306),
            NewVector3(109, 86, 1324),
            NewVector3(105, 83, 1342),
            NewVector3(137, 83, 1337)
        }
    },
    ["3_ExpandedStore"] = {
        [1] = {
            NewVector3(106, 59, 1283),
            NewVector3(125, 59, 1338),
            NewVector3(137, 59, 1337)
        },
        [2] = {
            NewVector3(108, 83, 1286),
            NewVector3(110, 83, 1298),
            NewVector3(130, 83, 1295),
            NewVector3(133, 83, 1313),
            NewVector3(112, 83, 1318),
            NewVector3(113, 83, 1328),
            NewVector3(137, 83, 1337)
        }
    },
    ["4_CameraFloors"] = {
        [1] = {
            NewVector3(141, 59, 1276),
            NewVector3(143, 59, 1288),
            NewVector3(112, 59, 1293),
            NewVector3(114, 59, 1308),
            NewVector3(146, 59, 1303),
            NewVector3(147, 59, 1317),
            NewVector3(118, 59, 1323),
            NewVector3(120, 59, 1340),
            NewVector3(139, 59, 1337)
        },
        [2] = {
            NewVector3(141, 83, 1277),
            NewVector3(148, 83, 1307),
            NewVector3(131, 83, 1338),
            NewVector3(137, 83, 1337)
        }
    },
    ["5_TheCEO"] = {
        [1] = {
            NewVector3(119, 60, 1282),
            NewVector3(137, 59, 1336)
        },
        [2] = {
            NewVector3(132, 83, 1291),
            NewVector3(100, 83, 1298),
            NewVector3(135, 83, 1338)
        }
    },
    ["6_LaserRooms"] = {
        [1] = {
            NewCFrame(109, 59, 1282),
            NewCFrame(122, 59, 1339),
            NewCFrame(134, 59, 1337)
        },
        [2] = {
            NewCFrame(124, 83, 1278),
            NewCFrame(134, 83, 1337)
        }
    }
}
local Locations1 = {
    ["Bank"]          = CFrame.new(-4, 18, 864),
    ["Jewelry Top"]    = CFrame.new(132, 119, 1331),
    ["Jewelry Bottom"] = CFrame.new(130, 18, 1395),
    ["Casino Top"]     = CFrame.new(44, 155, -4746),
    ["Casino Bottom"]  = CFrame.new(-207, 20, -4609),
    ["Donut"]         = CFrame.new(126, 19, -1628),
    ["Gas"]           = CFrame.new(-1564, 18, 636),
    ["Mansion"]       = CFrame.new(3042, 58, -4520),
    ["Museum"]        = CFrame.new(1017, 102, 1322),
    ["Power Plant"]    = CFrame.new(59, 21, 2342),
    ["Tomb"]          = CFrame.new(602, 21, -466)
}
local Locations2 = {
    ["Airport"]      = CFrame.new(-1447, 42, 2979),
    ["Season"]       = CFrame.new(-1319, 22, -861),
    ["Prison In"]     = CFrame.new(-1217, 18, -1782),
    ["Prison Out"]    = CFrame.new(-1154, 18, -1407),
    ["Volcano Base"]  = CFrame.new(2282, 19, -2016),
    ["City Base"]     = CFrame.new(-269, 18, 1608),
    ["Jetpack"]      = CFrame.new(-662, 218, -6009),
    ["Cargo Port"]    = CFrame.new(-381, 21, 2000),
    ["Control Tower"] = CFrame.new(83, 18, 1086),
    ["Gun Store"]     = CFrame.new(389, 19, 532),
    ["Trade Boat"]    = CFrame.new(2678, 24, -3829)
}

local OnOpen = Instance.new("BindableEvent")

local Robbery = setmetatable({
    Bank = {
        id        = RobberyConsts.ENUM_ROBBERY.BANK,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = true,
        Enabled   = true,
        GetPos    = function() return NewVector3(-8, 18, 865) end,
		GetModel  = function() return Bank end
    },
    Jewelry = {
        id        = RobberyConsts.ENUM_ROBBERY.JEWELRY,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = true,
        Enabled   = true,
        GetPos    = function() return NewVector3(63, 18, 1316) end,
		GetModel  = function() return Jewelry end
    },
    Museum = {
        id        = RobberyConsts.ENUM_ROBBERY.MUSEUM,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = true,
        Enabled   = true,
        GetPos    = function() return NewVector3(1066, 101, 1254) end,
		GetModel  = function() return Museum end
    },
    PowerPlant = {
        id        = RobberyConsts.ENUM_ROBBERY.POWER_PLANT,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = false,
        Enabled   = true,
        GetPos    = function() return NewVector3(68, 21, 2339) end,
		GetModel  = function() return PowerPlant end
    },
    PassengerTrain = {
        id        = RobberyConsts.ENUM_ROBBERY.TRAIN_PASSENGER,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = false,
        Enabled   = true,
        GetPos    = function() return HumanoidRootPart and HumanoidRootPart.Position + NewVector3(0, 2, 0) end
    },
    CargoTrain = {
        id        = RobberyConsts.ENUM_ROBBERY.TRAIN_CARGO,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = false,
        Enabled   = true,
        GetPos    = function() for i,v in pairs(CargoTrainBoxCars) do if Trains:FindFirstChild(v) then return Trains:FindFirstChild(v).Model.Rob.Gold.Position end end end
    },
    CargoShip = {
        id        = RobberyConsts.ENUM_ROBBERY.CARGO_SHIP,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = false,
        Enabled   = true,
        GetPos    = function() return HumanoidRootPart and HumanoidRootPart.Position + NewVector3(0, 1, 0) end
    },
    CargoPlane = {
        id        = RobberyConsts.ENUM_ROBBERY.CARGO_PLANE,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = false,
        Enabled   = true,
        GetPos    = function() return workspace:FindFirstChild("Plane") and workspace.Plane.PrimaryPart.Position end
    },
    Donut = {
        id        = RobberyConsts.ENUM_ROBBERY.STORE_DONUT,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = false,
        Enabled   = true,
        GetPos    = function() return NewVector3(80, 33, -1596) end
    },
    Gas = {
        id        = RobberyConsts.ENUM_ROBBERY.STORE_GAS,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = false,
        Enabled   = true,
        GetPos    = function() return NewVector3(-1603, 18, 662) end
    },
    Tomb = {
        id        = RobberyConsts.ENUM_ROBBERY.TOMB,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = true,
        Enabled   = true,
        GetPos    = function() return NewVector3(479, 20, -482) end,
		GetModel  = function() return Tomb end
    },
    Casino = {
        id        = RobberyConsts.ENUM_ROBBERY.CASINO,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = true,
        Enabled   = true,
        GetPos    = function() return NewVector3(46, 155, -4740) end,
		GetModel  = function() return Casino end
    },
    Mansion = {
        id        = RobberyConsts.ENUM_ROBBERY.MANSION,
        Open      = false,
        InstantTp = false,
        InstantTpSupported = true,
        Enabled   = true,
        GetPos    = function() return NewVector3(3032, 57, -4544) end,
		GetModel  = function() return MansionRobbery end
    },
    Airdrop = {
        Enabled = true,
        InstantTpSupported = false,
    }
}, {
	__index = {
		OnOpen = {
			Fire = function(self, ...)
				OnOpen:Fire(...)
			end,
			Connect = function(self, ...)
				OnOpen.Event:Connect(...)
			end
		}
	}
})

local MuseumObjects

spawn(function()
    WaitUntil(function()
        return Paintings
    end, nil, 1)

    MuseumObjects = {
        {
            Paintings["asimo3089"].Picture,
            NewCFrame(1089, 106, 1326)
        },
        {
            Paintings["badcc"].Picture,
            NewCFrame(1140, 106, 1261)
        },
        {
            CenterItems.TombLantern,
            NewCFrame(1089, 106, 1314)
        },
        {
            CenterItems.Mask,
            NewCFrame(1127, 106, 1264)
        },
        {
            CenterItems.DinoEgg,
            NewCFrame(1130, 106, 1343)
        },
        {
            CenterItems.DinoArm.DinoArm,
            NewCFrame(1167, 106, 1297)
        },
        {
            Museum.EgyptianCase.Relic.Relic,
            NewCFrame(1173, 102, 1260)
        },
        {
            Museum.JewelCase.Jewel.Jewel,
            NewCFrame(1093, 102, 1362)
        }
    }
end)
local AutoArrestMessages = {
	"Buy Jailbreaker V2 NOW or a scarry person will appear in your bed tonight!",
    ".gg/autoarrest > Use now for FREE!",
    ".gg/autoarrest > Buy right now.",
    "We also have a website! jailbreaker.site",
    "Check out our website! jailbreaker.site",
    "Join our community! .gg/autoarrest",
    "Jailbreak campers ware a thing but now.. Oh boy..",
    "Autoarrest on top tbh.",
    "I'm cool unlike you nerds.",
    "I'm not cheating.",
    "I just bought a new gaming chair!!",
    ".gg/autoarrest > Join and be part of the cool gang.",
    "It's just lag.",
    "Autoarrest is FREE!",
	"Autorob is PAID!",
    "Jailbreaker V2 > The BEST autorob for Jailbreak!",
    "Jailbreaker V2 > The BEST autoarrest for Jailbreak!",
    "Autoarrest created by MinWasTaken & Brizzy!",
    "Autoarrest NOW better than ever!"
}
local ItemsType = {
	"HyperChrome",
    'Legendary',
    'Epic',
    'Ultra Rare',
    'Rare',
    'Common'
}
getgenv().RemoteEvent = getgenv().RemoteEvent or getupvalue(getupvalue(Event.FireServer, 1), 2)

--[[ Exploit Functions ]]

local SetThread  = (syn and syn.set_thread_identity) or setthreadcontext
local Request    = (syn and syn.request) or (http and http.request) or request

--[[ Dev Commands & Serverhop On Auto Arrester]]

function Say(Message)
	TextChatService.TextChannels.RBXGeneral:SendAsync(Message)
end

TextChatService.TextChannels.RBXGeneral.MessageReceived:Connect(function(Filtered)
	local Player = Filtered.TextSource
	local Message = string.gsub(Filtered.Text, "<[^>]*>", "")
	local Commands = {";bounty", ";bring", ";start", ";info", ";kill"}

	if table.find(AutoArrestMessages, Message) and Settings.ServerhopOnAutoArrest then
		SwitchServer(Settings.SmallServer)
	elseif table.find(Commands, Message) and Request({Url="https://autoarrest.jailbreaker.site/checkdev/"..tostring(Player.UserId)})["Body"] == "yes" then
		if Message == ";bounty" then
			if not PlayerGui.AppUI.Buttons:FindFirstChild("Bounty") then
				return
			end
			
			local Bounty = ""
			local BountyString = PlayerGui.AppUI.Buttons.Bounty.Label.Text
	
			for Number in string.gmatch(BountyString, "%d+") do
				Bounty = Bounty..tostring(Number)
			end

			Say("My current bounty is "..tostring(Bounty).."!")
		elseif Message == ";start" then
			if AutoRobbing then
				Say("Autorob is already enabled.")

				return
			end

			ToggleAutoRob(true)
		elseif Message == ";info" then
			pcall(function()
				local DiscordName = Request({Url="https://discordlookup.mesavirep.xyz/v1/user/"..tostring(DiscordID)})["Body"]["global_name"]

				Say("I am "..DiscordName.."!")
			end)
			
			Say("I have "..tostring(ExecutionCount).." executions!")
			Say("Script active for "..tostring(GetTimeElapsed()).."!")
		elseif Message == ";kill" then
			Say("*Insert oof sound here*")
			Character.Head:BreakJoints()
		elseif Message == ";bring" then
			if AutoRobbing then
				Say("I am disabling autorob, please wait.")
				ToggleAutoRob(false)

				WaitUntil(function()
					return not AutoRobbing
				end)
			end

			if Settings.KillAura then
				Say("I am disabling killaura, please wait.")

				Settings.KillAura = false
			end

			Say("I am teleporting, please wait.")

			if Raycast(HumanoidRootPart.Position, Sky) then
				local Teleporter  = GetNearestTeleporter()
				local Inside      = Teleporter.Inside
				local Outside     = Teleporter.Outside
				local Success     = false
				local Signal      = HumanoidRootPart:GetPropertyChangedSignal("CFrame"):Connect(function()
					if Distance(HumanoidRootPart.Position, Outside) < 10 then
						Success   = true
					end
				end)
	
				local Try = tick()
				
				while Success == false do
					if Check() then
						Signal:Disconnect()
						WaitUntil(function()
							return not Check()
						end)

						return error()
					end
	
					HumanoidRootPart.CFrame = NewCFrame(Inside)
	
					if tick() - Try > 3 then
						wait(3)
						Try = tick()
					else
						wait()
					end
	
					wait()
				end
				
				Signal:Disconnect()
				wait(1)
			end

			if not Player.Character:FindFirstChild("HumanoidRootPart") then
				Say("I am waiting for your HumanoidRootPart!")

				WaitUntil(function()
					return Player.Character:FindFirstChild("HumanoidRootPart")
				end)
			end

			Say("I am teleporting 200 studs above you!")

			Teleport(Player.Character.HumanoidRootPart.CFrame+Vector3.new(0, 200, 0), "Vehicle")

			Say("I have arrived!")
		end
	end
end)

--[[ Other Variables ]]

local wait          = task.wait
local spawn         = task.spawn
local RaycastParams = RaycastParams.new()

if JB_DEBUG then
	warn("[Jailbreaker Debugging]: Loading Math Functions..")
end

--[[ Init ]]
--// Physics Functions

function XZ(Vector3)
    return NewVector3(Vector3.X, 0, Vector3.Z)
end

function Distance(Start, End)
    return (Start - End).Magnitude
end

function DistanceXZ(Start, End)
    return Distance(XZ(Start), XZ(End))
end

function ToSky(Vector3, Y)
    return XZ(Vector3) + (Y and NewVector3(0, 1, 0) * Y or Sky)
end

--// Character

function LagBackCheck(Part, Stud)
    local OldPosition
	local YLagBackTick

    local Signal = Part:GetPropertyChangedSignal("Position"):Connect(function()
		local CurrentPosition = Part.Position

        if DistanceXZ(CurrentPosition, OldPosition) > Stud then
			print(DistanceXZ(CurrentPosition, OldPosition))
			LaggedBack = true
			warn("Lagback Detected!")

			delay(1, function()
				LaggedBack = false
			end)
		elseif math.abs(CurrentPosition.Y - OldPosition.Y) > Stud then
			if YLagBackTick and tick() - YLagBackTick < 2 then
				LaggedBack = true
				warn("Lagback Detected!")

				delay(1, function()
					LaggedBack = false
				end)
			end
			YLagBackTick = tick()
		end
		
		OldPosition = CurrentPosition
	end)

    spawn(function()
        while Signal do
            OldPosition = Part.Position
            RunService.Stepped:Wait()
        end
    end)

    return {
        Stop = function()
			if Signal then
				Signal:Disconnect()
				Signal = nil
			end
        end
    }
end

-- local BindableEvent = Instance.new("BindableEvent")
-- local OnCharacterAdded = {
-- 	Fire = function(self, ...)
-- 		BindableEvent:Fire(...)
-- 	end,
-- 	Connect = function(self, ...)
-- 		BindableEvent.Event:Connect(...)
-- 	end
-- }

function UpdateCharacter(Char)
    if Char then
        Character        = Char
        Humanoid         = Char:WaitForChild("Humanoid")
        HumanoidRootPart = Char:WaitForChild("HumanoidRootPart")
        Died             = false
        Arrested         = false
        --// Check Lagback
        local Check      = LagBackCheck(HumanoidRootPart, 10)
        --// Insert New Character To Raycast's Ignore List
        RaycastIgnoreList[#RaycastIgnoreList + 1] = Char
        --// Arrested Check
        function OnChildAdded(Child)
            
        end
        function OnChildRemoved(Child)
            
        end
        Character.ChildAdded:Connect(OnChildAdded)
        Character.ChildRemoved:Connect(OnChildRemoved)
        --// Died Check
        function OnDied()
            Character        = nil
            Humanoid         = nil
            HumanoidRootPart = nil
            Died             = true
            --// Stop Lagback check
            Check:Stop()

            --// Disconnect Stepped Signals
            for i,v in pairs(SteppedSignals) do
                v:Disconnect()
            end
        end

        Humanoid.Died:Connect(OnDied)
		
		--Humanoid:GetPropertyChangedSignal("Parent"):Connect(OnDied)
		--OnCharacterAdded:Fire(Character)
    end
end

if LocalPlayer.Character then
    UpdateCharacter(LocalPlayer.Character)
end

LocalPlayer.CharacterAdded:Connect(UpdateCharacter)

--// Raycast

function Raycast(Start, Direction)
	RaycastParams.FilterDescendantsInstances = RaycastIgnoreList

	return workspace:Raycast(Start, Direction, RaycastParams)
end

--// Anti AFK

for i, Connection in pairs(getconnections(LocalPlayer.Idled)) do
    Connection:Disable()
end

--// No Fall Damage

TagUtils.isPointInTag = function(Point, Tag)
	if Tag == "NoRagdoll" or Tag == "NoFallDamage" --[[or Tag == "NoParachute"]] then
		return true
	end
    return isPointInTag(Point, Tag)
end

--// Give Key

PlayerUtils.hasKey = function()
    return true
end

--// No Vehicle Field Of View

-- Camera:GetPropertyChangedSignal("FieldOfView"):Connect(function()
--     Camera.FieldOfView = 70
-- end)

--// Safe Platfarm & Platform

local Platform    = workspace:FindFirstChild("JailbreakerV2") or Instance.new("Part", workspace)
Platform.Name     = "JailbreakerV2"
Platform.Size     = NewVector3(100, 1, 100)
Platform.Anchored = true
Platform.Position = Vector3.new(0, 100000, 0)
Platform.Transparency = 1

--// Raycast's Ignore List

function OnChildAdded(Child)
	if Child.Name == "Cuffed" then
		Arrested = true
    elseif table.find(RaycastIgnorable, Child.Name) then
        RaycastIgnoreList[#RaycastIgnoreList + 1] = Child
    end
end

function OnChildRemoved(Child)
	if Child.Name == "Cuffed" then
		Arrested = false
	elseif table.find(RaycastIgnorable, Child.Name) then
        table.remove(RaycastIgnoreList, table.find(RaycastIgnoreList, Child))
    end
end

workspace.ChildAdded:Connect(OnChildAdded)
workspace.ChildRemoved:Connect(OnChildRemoved)

for i,v in pairs(workspace:GetChildren()) do
    OnChildAdded(v)
end

for i,v in pairs(CollectionService:GetTagged("Tree")) do
    RaycastIgnoreList[#RaycastIgnoreList + 1] = v
end
for i,v in pairs(CollectionService:GetTagged("NoClipAllowed")) do
    RaycastIgnoreList[#RaycastIgnoreList + 1] = v
end

RaycastParams.FilterType = Enum.RaycastFilterType.Exclude

--// Disable Door Collision
function DoorAdded(Door)
	if Door:FindFirstChild("Model") then
		RaycastIgnoreList[#RaycastIgnoreList + 1] = Door.Model

		for i2,v2 in pairs(Door.Model:GetChildren()) do
			if v2:IsA("BasePart") then
				v2.CanCollide = false
			end
		end
	end

	local Touch = Door:FindFirstChild("Touch")

	if not Touch or not Touch:IsA("BasePart") then
		return
	end

	local A = false
	local B = false

	for Lerp = 0, 50, 10 do
		if A and B then
			break
		end

		local Front  = Touch.Position + (Touch.CFrame.LookVector * Lerp)
		local Behind = Touch.Position + (Touch.CFrame.LookVector * -Lerp)

		if not Raycast(Touch.Position, Front - Touch.Position) and not Raycast(Front, Sky) and not A then
			EscapeExits[#EscapeExits + 1] = Front
			A = true
		end
		if not Raycast(Touch.Position, Behind - Touch.Position) and not Raycast(Behind, Sky) and not B then
			EscapeExits[#EscapeExits + 1] = Behind
			B = true
		end
	end
end

for i,v in pairs(CollectionService:GetTagged("Door")) do
    DoorAdded(v)
end
CollectionService:GetInstanceAddedSignal("Door"):Connect(function(v)
	DoorAdded(v)
end)

--// Client Anti Cheat Bypass

-- realise this shit isnt working smh :sob:
-- getsenv(LocalPlayer.PlayerScripts.LocalScript).pcall = function()
--     return true
-- end

if JB_DEBUG then
	warn("[Jailbreaker Debugging]: Disabling Client Cheat Detections..")
end

for i,v in pairs(getgc(true)) do
	if type(v) == "table" then
		if rawget(v, "getRemainingDebounce") and type(v.getRemainingDebounce) == "function" then
			GarageUtils = v
		end
	elseif type(v) == "function" and islclosure(v) and debug.info(v, "n"):match("CheatCheck") then
        if LPH_OBFUSCATED then
            LPH_NO_VIRTUALIZE(function()
                hookfunction(v, function() end)
            end)()
        else
            hookfunction(v, function() end)
        end
		warn("[Jailbreaker Debugging]: Successfully Disabled Client Cheat Detecions!")
	end
end

GetRemainingDebounce = GarageUtils.getRemainingDebounce
OnClickSpawnVehicle  = GarageUtils.onClickSpawnVehicle

--// Disable NPCs

NPC.new = function(NPCObject, ...)
    if NPCObject.Name ~= "ActiveBoss" then
    	NPCObject:Destroy()
        return
    end
    return NPC_new(NPCObject, ...)
end

--// Disable Mansion Boss Attacks
BossNPCBinder._constructor.PlayArmGrab          = Maid_new
BossNPCBinder._constructor.PlayMansionLasers    = Maid_new
BossNPCBinder._constructor.PlayAuraBlast        = Maid_new
BossNPCBinder._constructor.PlayLaserSweepVisual = Maid_new
BossNPCBinder._constructor.PlayCallInGuards     = Maid_new
BossNPCBinder._constructor.PlayMansionCameras   = Maid_new

--// Disable projectiles
MilitaryTurret._fire  = function() end
DartDispenser._fire   = function() end
CargoShipTurret.Shoot = function() end

--// You cannot lock your car here. & Tasers not allowed here.
Notification.new = function(NotificationData)
    if NotificationData.Text == "You cannot lock your car here." or NotificationData.Text == "Tasers not allowed here." or NotificationData.Text == "Vault must be armed to crack it!" then
        return
    end

    return Notification_new(NotificationData)
end

--// Switch Server On Kick
CoreGui.RobloxPromptGui.promptOverlay.ChildAdded:Connect(function(Child)
    if Child.Name == "ErrorPrompt" and Child:FindFirstChild("MessageArea") and Child.MessageArea:FindFirstChild("ErrorFrame") then
        SwitchServer(Settings.SmallServer)
    end
end)

--// Robbery Status
for i,v in pairs(RobberyState:GetChildren()) do
    for i2,v2 in pairs(Robbery) do
        if v.Name == tostring(v2.id) then
            if i2 == "Museum" or i2 == "Tomb" then
                v2.Open = (v.Value == 2)
            elseif i2 == "Mansion" then
                v2.Open = (v.Value == 1)
            else
                v2.Open = (v.Value ~= 3)
            end

			Robbery.OnOpen:Fire(i2, v2.Open)

            v:GetPropertyChangedSignal("Value"):Connect(function()
                if i2 == "Museum" or i2 == "Tomb" then
                    v2.Open = (v.Value == 2)
                elseif i2 == "Mansion" then
                    v2.Open = (v.Value == 1)
                else
                    v2.Open = (v.Value ~= 3)
                end

				Robbery.OnOpen:Fire(i2, v2.Open)
            end)

            break
        end
    end
end

RobberyState.ChildAdded:Connect(function(v)
    for i2,v2 in pairs(Robbery) do
        if v.Name == tostring(v2.id) then
            if i2 == "Museum" or i2 == "Tomb" then
                v2.Open = (v.Value == 2)
            elseif i2 == "Mansion" then
                v2.Open = (v.Value == 1)
            else
                v2.Open = (v.Value ~= 3)
            end

            v:GetPropertyChangedSignal("Value"):Connect(function()
                if i2 == "Museum" or i2 == "Tomb" then
                    v2.Open = (v.Value == 2)
                elseif i2 == "Mansion" then
                    v2.Open = (v.Value == 1)
                else
                    v2.Open = (v.Value ~= 3)
                end
            end)

            break
        end
    end
end)

--// Arrested Check

Inventory.ChildAdded:Connect(OnChildAdded)
Inventory.ChildRemoved:Connect(OnChildRemoved)

for i,v in pairs(Inventory:GetChildren()) do
	OnChildAdded(v)
end

if CellTime.Visible then
	Arrested = true
end

CellTime:GetPropertyChangedSignal("Visible"):Connect(function()
	if CellTime.Visible then
		Arrested = true
	else
		Arrested = false
	end
end)

--// Some Functions Idk

local TeamSwitchFunc = nil
local TeamJoinFunc   = getconnections(TeamGui.Container.ContainerPlay.Play.MouseButton1Down)[1] and getconnections(TeamGui.Container.ContainerPlay.Play.MouseButton1Down)[1].Function

local TeamSwitchOnClick = BigButtonService.active[2].onClick

if getupvalue(TeamSwitchOnClick, 1) ~= nil then
    TeamSwitchOnClick()
end

setupvalue(TeamSwitchOnClick, 2, {
	new = function()
		return {
			OnYes = {
				Connect = function(self, func)
					TeamSwitchFunc = func
				end
			},
			OnNo = {
				Connect = function() end
			},
			Destroy = function() end
		}
	end
})

TeamSwitchOnClick()
TeamSwitchOnClick()
setupvalue(TeamSwitchOnClick, 2, Confirmation)

local Connections       = getconnections(CollectionService:GetInstanceAddedSignal("CargoPlaneTalkie"))
local InstanceAddedFunc = #Connections > 0 and Connections[1].Function
local CallPlaneCallback = InstanceAddedFunc and getupvalue(InstanceAddedFunc, 1) or (function()
    for i,v in pairs(Specs) do
        if v.Name == "Call Cargo Plane" then
            return v.Callback
        end
    end
end)()

if not CallPlaneCallback then
    setclipboard(string.format([[
        INFO : PLANE_CALLBACK_NIL
        EXECUTOR : %s
    ]], identifyexecutor()))
    Notification_new({
        Text = "Something went wrong while loading Jailbreaker. Info has been copied to your clipboard. Jailbreaker will proceed to run.",
        Duration = 10
    })
end

--[[ No Lasers ]]

function RemoveLaser(Part)
    --Part.CFrame = CFrame.new(math.huge, math.huge, math.huge)
    Part.CanTouch = false
    --Part.CanCollide = false
    --Part.Transparency = 1
end

--// Jewelry

local TouchClasses = {
    "TouchInterest",
    "TouchTransmitter"
}

spawn(function()
    WaitUntil(function()
        return workspace:FindFirstChild("Jewelrys")
    end, nil, 1)

    WaitUntil(function()
        return workspace.Jewelrys:GetChildren()[1]
    end, nil, 1)

    Jewelry = workspace.Jewelrys:GetChildren()[1]
    Boxes   = Jewelry:WaitForChild("Boxes", 9999)

    for i,v in pairs(Jewelry:GetDescendants()) do
        if table.find(TouchClasses, v.ClassName) and v.Parent.Name ~= "LaserTouch" then
            RemoveLaser(v.Parent)
            RaycastIgnoreList[#RaycastIgnorable + 1] = v.Parent
        end
        if v:IsA("BasePart") and not v.CanCollide then
            RaycastIgnoreList[#RaycastIgnorable + 1] = v
        end
    end

    Jewelry.DescendantAdded:Connect(function(v)
        if table.find(TouchClasses, v.ClassName) and v.Parent.Name ~= "LaserTouch" then
            RemoveLaser(v.Parent)
            RaycastIgnoreList[#RaycastIgnorable + 1] = v.Parent
        end
        if v:IsA("BasePart") and not v.CanCollide then
            RaycastIgnoreList[#RaycastIgnorable + 1] = v
        end
    end)
end)

--// Bank

spawn(function()
    WaitUntil(function()
        return workspace:FindFirstChild("Banks")
    end, nil, 1)

    WaitUntil(function()
        return workspace.Banks:GetChildren()[1]
    end, nil, 1)

    Bank = workspace.Banks:GetChildren()[1]

    local Layout = Bank.Layout:GetChildren()[1]

    if Layout:FindFirstChild("Lasers") then
        for i,v in pairs(Layout.Lasers:GetDescendants()) do
            if table.find(TouchClasses, v.ClassName) then
                RemoveLaser(v.Parent)
            end
        end
    end

    Bank.Layout.ChildAdded:Connect(function(Layout)
        if Layout:FindFirstChild("Lasers") then
            for i,v in pairs(Layout.Lasers:GetDescendants()) do
                if table.find(TouchClasses, v.ClassName) then
                    RemoveLaser(v.Parent)
                end
            end
        end
    end)
end)

--// Museum

spawn(function()
    WaitUntil(function()
        return workspace:FindFirstChild("Museum")
    end, nil, 1)

    Museum      = workspace.Museum
    Paintings   = Museum:WaitForChild("Paintings", 9999)
    CenterItems = Museum:WaitForChild("CenterItems", 9999)
    
    for i, v in pairs(Museum:GetDescendants()) do
        if table.find(TouchClasses, v.ClassName) then
            RemoveLaser(v.Parent)
        end
    end

    Museum.DescendantAdded:Connect(function(v)
        if table.find(TouchClasses, v.ClassName) then
            RemoveLaser(v.Parent)
        end
    end)
end)

--// Mansion

spawn(function()
    WaitUntil(function()
        return workspace:FindFirstChild("MansionDecorative")
    end, nil, 1)

    for i,v in pairs(workspace.MansionDecorative:GetChildren()) do
        if v.Name == "BarbedWire" then
            RemoveLaser(v)
        end
    end

    workspace.MansionDecorative.ChildAdded:Connect(function(v)
        if v.Name == "BarbedWire" then
            RemoveLaser(v)
        end
    end)
end)
spawn(function()
    WaitUntil(function()
        return workspace:FindFirstChild("MansionRobbery")
    end, nil, 1)
    WaitUntil(function()
        return workspace.MansionRobbery:FindFirstChild("Lasers") and workspace.MansionRobbery:FindFirstChild("LaserTraps")
    end, nil, 1)

    for i,v in pairs(workspace.MansionRobbery.Lasers:GetDescendants()) do
        if table.find(TouchClasses, v.ClassName) then
            RemoveLaser(v.Parent)
        end
    end
	for i,v in pairs(workspace.MansionRobbery.LaserTraps:GetDescendants()) do
        if table.find(TouchClasses, v.ClassName) then
            RemoveLaser(v.Parent)
        end
    end

    workspace.MansionRobbery.Lasers.DescendantAdded:Connect(function(v)
        if table.find(TouchClasses, v.ClassName) then
            RemoveLaser(v.Parent)
        end
    end)
	workspace.MansionRobbery.LaserTraps.DescendantAdded:Connect(function(v)
        if table.find(TouchClasses, v.ClassName) then
            RemoveLaser(v.Parent)
        end
    end)
end)

--// Tomb

spawn(function()
    for i,v in pairs(CollectionService:GetTagged("TombSpike")) do
		RemoveLaser(v.InnerModel.Door)
	end
	
	CollectionService:GetInstanceAddedSignal("TombSpike"):Connect(function(v)
		RemoveLaser(v.InnerModel.Door)
	end)
end)

--// Other Lasers

for i,v in pairs(CollectionService:GetTagged("BarbedWireClient")) do
    RemoveLaser(v)
end

--// Laser Added Check

CollectionService:GetInstanceAddedSignal("BarbedWireClient"):Connect(function(v)
    RemoveLaser(v)
end)
 
--// Disable Casino Invisible Part Collision

spawn(function()
    WaitUntil(function()
        return Casino
    end, nil, 1)

    for i,v in pairs(Casino.Elevator.Car.InnerModel.Model:GetChildren()) do
        if v.Name == "InvisiblePart" then
            v.CanCollide = false
        end
    end
end)

--[[ Functions ]]
--// Character

function Check()
	return Died or Arrested
end

function WaitForRespawn()
	wait()
	
    WaitUntil(function()
    	return not Died
	end)
	
	wait(3)
end

function AttemptJump()
	warn(debug.traceback())

    if Died then
		WaitForRespawn()
		return error()
	end
    
    if Character:FindFirstChild("InVehicle") then
        while Character:FindFirstChild("InVehicle") do
            if Died then
                WaitForRespawn()
                return error()
            end

            OnJump()

            WaitUntil(function()
                return not Character:FindFirstChild("InVehicle")
            end, 5)

			wait()
        end
    elseif (Humanoid.Sit and not Settings.AntiArrest) or GetCartForCharacter(Character) then
        while (Humanoid.Sit and not Settings.AntiArrest) or GetCartForCharacter(Character) do
            if Died then
                WaitForRespawn()
                return error()
            end

            OnJump()

            Humanoid.Jump = true
            Humanoid.Sit  = false

            WaitUntil(function()
                return (not Humanoid.Sit and not Settings.AntiArrest) or not GetCartForCharacter(Character)
            end, 3)

			wait()
        end
    end
end

function Die()
    warn(debug.traceback())
    
    if Died then
        return
    end

    AttemptJump()

	Pcall(function()
		Humanoid.Sit = false
		EnteringCar = true

		delay(0.5, function()
			EnteringCar = false
		end)
	end)

    Character.Head:BreakJoints()

	ReplicatedStorage.SpawnSelectionUpdateSpawnData:FireServer(nil)
	ReplicatedStorage.SpawnSelectionSelect:FireServer("City Base")
end

--// Settings

local DefaultSettings = {
    PlayerTpSpeed = 83,
    VehicleTpSpeed = 400,
    GroundTpSpeed = 43,
	TeleportMethod = "V2",

    KillAura = false,
    KillAuraGun = "Pistol",
	KillAuraExclude = {},

    PlaneWaitBeforeSell = 5,
	MuseumSellWait = 20,
    PowerPlantUraniumValue = 6000,
    Cooldown = 0,
    BagSellValue = 999999,

    AutoCallPlane = false,
    AutoOpenSafe = false,
    AutoBuySafe = false,
    AutoSwitchServer = false,
    AutoPullMuseumLever = false,

    InstantEscape = false,
    RobberySortType = "Index",

    AutoRob = false,
	AntiArrest = false,
    RobberyTogglesOff = {},
    InstantRobberyTp = false,

	HideUIOnNewServer = false,
	SmallServer = false,

	WebhookEnabled = false,
	RewardSpinnerNotifier = false,
	RewardSpinnerItems = {}
}

for k,v in pairs(DefaultSettings) do
    if Settings[k] == nil then
        Settings[k] = v
    end
end

if not JBV2 and isfile("JailbreakerV2_Settings.json") then
    local SavedSettings

    Pcall(function()
        SavedSettings = HttpService:JSONDecode(readfile("JailbreakerV2_Settings.json"))
    end, "LoadJailbreakerConfig", "Failed To Parse JailbreakerV2_Settings.json. Seem Like The File Was Corrupted. Please Delete The File To Fix The Issue. If This Keep Happening, Please Report This To The Developers To Get This Issue Fixed. "..identifyexecutor().."/workspace/JailbreakerV2_Settings.json")

    if SavedSettings then
        for k,v in pairs(DefaultSettings) do
            if SavedSettings[k] == nil then
                SavedSettings[k] = v
            end
        end
        for k,v in pairs(SavedSettings) do
            Settings[k] = v
        end
    end
end

if Settings.InstantRobberyTp then
    for k,v in pairs(Robbery) do
        v.InstantTp = true
    end
end

for k,v in pairs(Settings.RobberyTogglesOff) do
    Robbery[k].Enabled = not v
end

if JB_DEBUG then
	warn("[Jailbreaker Debugging]: Loading Teleportation Functions..")
end

--[[ Teleportation ]]
--// Pathfinder

for i,v in pairs(workspace:GetDescendants()) do
    if v:IsA("BasePart") and v.CanCollide == false then
        RaycastIgnoreList[#RaycastIgnoreList + 1] = v
    end
end

local Pathfinder = {}

do
	-- local RaycastParams = RaycastParams.new()
	-- local Pathfinder = {}

	-- local function Raycast(Start, Direction)
		-- return workspace:Raycast(Start, Direction, RaycastParams)
	-- end

	local function Blockcast(Start, Size, Direction)
		return workspace:Blockcast(CFrame.new(Start), Size, Direction, RaycastParams)
	end

	function Pathfinder.IgnoreList(IgnoreList)
		local OldIgnoreList = RaycastParams.FilterDescendantsInstances
		
		for i,v in pairs(IgnoreList) do
			table.insert(OldIgnoreList, v)
		end
		
		RaycastParams.FilterType                 = Enum.RaycastFilterType.Exclude
		RaycastParams.FilterDescendantsInstances = OldIgnoreList
	end

	function Pathfinder.FindPath(StartPosition, EndPosition, Radius, WaypointSpacing)
		RaycastParams.FilterDescendantsInstances = RaycastIgnoreList

		if workspace:FindFirstChild("Path") then
			Pathfinder.IgnoreList({workspace.Path})
		end
		
		local Grid      = {}
		local OpenSet   = {}

		local FloorX = math.floor(StartPosition.X)
		local FloorY = math.floor(StartPosition.Y)
		local FloorZ = math.floor(StartPosition.Z)

		StartPosition = Vector3.new(FloorX, FloorY, FloorZ)
		
		if not workspace:FindFirstChild("Nodes") then
			Instance.new("Folder", workspace).Name = "Nodes"
			
			Pathfinder.IgnoreList({workspace.Nodes})
		end
		
		workspace.Nodes:ClearAllChildren()

		local function NewNode(Position)
			-- local Node      = Instance.new("Part", workspace.Nodes)
			-- Node.Size       = Vector3.new(1, 1, 1)
			-- Node.Position   = Position
			-- Node.Anchored   = true
			-- Node.BrickColor = BrickColor.Red()
			-- Node.CanCollide = false
			
			local NodeTable = {}

			NodeTable.Position = Position
			NodeTable.Parent   = nil
			NodeTable.HCost    = (EndPosition - Position).Magnitude
			
			--NodeTable.Node     = Node

			if not Grid[Position.X] then
				Grid[Position.X] = {}
			end
			if not Grid[Position.X][Position.Y] then
				Grid[Position.X][Position.Y] = {}
			end

			Grid[Position.X][Position.Y][Position.Z] = NodeTable

			return NodeTable
		end

		local StartNode = NewNode(StartPosition)
		local Start = tick()

		table.insert(OpenSet, StartNode)

		while #OpenSet > 0 and tick() - Start < 7 do
			for Boost = 1, 25 do
				if #OpenSet == 0 then
					break
				end

				local Winner = 1

				for i = 1, #OpenSet do
					if OpenSet[i].HCost < OpenSet[Winner].HCost then
						Winner = i
					end
				end

				local Current = table.remove(OpenSet, Winner)

				if (Current.Position - EndPosition).Magnitude < WaypointSpacing then
					if not Blockcast(Current.Position, Vector3.new(Radius, 0, Radius), EndPosition - Current.Position) then
						local Waypoints         = {}

						while true do
							table.insert(Waypoints, 1, Current.Position)

							if not Current.Parent then
								break
							end

							Current = Current.Parent
						end

						table.insert(Waypoints, EndPosition)

						for Round = 1, 3 do
							local SmoothedWaypoints = {}
							
							for i = 1, #Waypoints - 1 do
								local Dir = Waypoints[i + 1] - Waypoints[i]
								
								if Dir.Magnitude == 0 then
									continue
								end
								
								for Lerp = 0, Dir.Magnitude, 1 do
									table.insert(SmoothedWaypoints, Waypoints[i] + (Dir.Unit * Lerp))
								end

							    table.insert(SmoothedWaypoints, Waypoints[i + 1])
							end
							
							Waypoints         = SmoothedWaypoints
							SmoothedWaypoints = {}
							
							local Current     = 1
							local A, B        = false, false
							
							table.insert(SmoothedWaypoints, Waypoints[Current])

							for i = 2, #Waypoints - 1 do
								if i <= Current then
									continue
								end

								--if Raycast(Waypoints[i], Vector3.new(0, -2, 0)) then
								--	Waypoints[i] = Waypoints[i] + Vector3.new(0, 2, 0)
								--end
								--if Raycast(Waypoints[i], Vector3.new(0, 2, 0)) then
								--	Waypoints[i] = Waypoints[i] + Vector3.new(0, -2, 0)
								--end
								
								if Blockcast(Waypoints[Current], Vector3.new(Radius, 0, Radius), Waypoints[i + 1] - Waypoints[Current]) then
									if Raycast(Waypoints[Current] + Vector3.new(0, -3, 0), Waypoints[i] - Waypoints[Current]) then
										Waypoints[i] = Waypoints[i] + Vector3.new(0, 3, 0)
									end
									if Raycast(Waypoints[Current] + Vector3.new(0, 3, 0), Waypoints[i] - Waypoints[Current]) then
										Waypoints[i] = Waypoints[i] + Vector3.new(0, -3, 0)
									end
									
									table.insert(SmoothedWaypoints, Waypoints[i])
									
									Current = i
								end
							end
							
							table.insert(SmoothedWaypoints, Waypoints[#Waypoints])

							Waypoints = SmoothedWaypoints
						end
						
						--for Smoothness = 1, 2 do
						--	local NewWaypoints = {}

						--	for i = 1, #Waypoints - 1 do
						--		local Dir = Waypoints[i + 1] - Waypoints[i]

						--		for Lerp = 0, Dir.Magnitude, 2 do
						--			table.insert(NewWaypoints, Waypoints[i] + (Dir.Unit * Lerp))
						--		end

						--		table.insert(NewWaypoints, Waypoints[i + 1])
						--	end

						--	Waypoints = NewWaypoints

						--	local NewWaypoints = {}
							
						--	--local Skip = 0

						--	--table.insert(NewWaypoints, Waypoints[1])

						--	--for i = 1, #Waypoints do
						--	--	if i < Skip then
						--	--		continue
						--	--	end

						--	--	for i2 = #Waypoints, i + 1, -1 do
						--	--		if not Blockcast(Waypoints[i] + Vector3.new(0, 2, 0), Vector3.new(Radius, 0, Radius), (Waypoints[i2] + Vector3.new(0, 2, 0)) - (Waypoints[i] + Vector3.new(0, 2, 0))) then
						--	--			if Raycast(Waypoints[i] - Vector3.new(0, 3, 0), (Waypoints[i2] - Vector3.new(0, 3, 0)) - (Waypoints[i] - Vector3.new(0, 3, 0))) then
						--	--				NewWaypoints[#NewWaypoints] = NewWaypoints[#NewWaypoints] + Vector3.new(0, 3, 0)
						--	--				Waypoints[i2] = Waypoints[i2] + Vector3.new(0, 3, 0)
						--	--			end
										
						--	--			--local Dir = Waypoints[i2] - Waypoints[i]

						--	--			--for Lerp = 0, Dir.Magnitude, 4 do
						--	--			--	table.insert(NewWaypoints, Waypoints[i] + (Dir.Unit * Lerp))
						--	--			--end

						--	--			--table.insert(NewWaypoints, Waypoints[i2])

						--	--			table.insert(NewWaypoints, Waypoints[i2])

						--	--			Skip = i2

						--	--			break
						--	--		end
						--	--	end
						--	--end
							
						--	local Current = Waypoints[1]
						--	local Skip    = 0
							
						--	table.insert(NewWaypoints, Current)
							
						--	for i = 1, #Waypoints + 1 do
						--		if i < Skip then
						--			continue
						--		end
								
						--		if i == #Waypoints + 1 or Blockcast(Current + Vector3.new(0, 2, 0), Vector3.new(Radius, 0, Radius), (Waypoints[i] + Vector3.new(0, 2, 0)) - (Current + Vector3.new(0, 2, 0))) then
						--			local v = Waypoints[i - 1]
									
						--			if Raycast(Current - Vector3.new(0, 3, 0), (v - Vector3.new(0, 3, 0)) - (Current - Vector3.new(0, 3, 0))) then
						--				NewWaypoints[#NewWaypoints] = NewWaypoints[#NewWaypoints] + Vector3.new(0, 3, 0)
						--				v = v + Vector3.new(0, 3, 0)
						--			end

						--			--local Dir = Waypoints[i2] - Waypoints[i]

						--			--for Lerp = 0, Dir.Magnitude, 4 do
						--			--	table.insert(NewWaypoints, Waypoints[i] + (Dir.Unit * Lerp))
						--			--end

						--			--table.insert(NewWaypoints, Waypoints[i2])

						--			table.insert(NewWaypoints, v)
									
						--			print(v)
						--			print(i - 1)
									
						--			Current = v
						--			Skip = i - 1

						--			break
						--		end
						--	end

						--	Waypoints = NewWaypoints
						--end
						
						return Waypoints
					end
				end

				for x = -WaypointSpacing, WaypointSpacing, WaypointSpacing do
					for y = -WaypointSpacing, WaypointSpacing, WaypointSpacing do
						for z = -WaypointSpacing, WaypointSpacing, WaypointSpacing do
							if x + y + z == 0 then
								continue
							end

							local NeighborPosition = Current.Position + Vector3.new(x, y, z)

							if Blockcast(Current.Position, Vector3.new(Radius, 0, Radius), NeighborPosition - Current.Position) then
								continue
							end

							local Neighbor

							if Grid[NeighborPosition.X] and Grid[NeighborPosition.X][NeighborPosition.Y] and Grid[NeighborPosition.X][NeighborPosition.Y][NeighborPosition.Z] then
								Neighbor = Grid[NeighborPosition.X][NeighborPosition.Y][NeighborPosition.Z]
							end

							if Neighbor then
								continue
							else
								local NewNeighbor  = NewNode(NeighborPosition)

								NewNeighbor.Parent = Current

								table.insert(OpenSet, NewNeighbor)
							end
						end
					end
				end
			end
			task.wait()
		end
	end

	function Pathfinder.DrawPath(Waypoints)
		if not workspace:FindFirstChild("Path") then
			Instance.new("Folder", workspace).Name = "Path"
		end
		
		for i = 1, #Waypoints - 1 do
			local Waypoint      = Instance.new("Part", workspace.Path)
			Waypoint.CFrame     = CFrame.lookAt(CFrame.new(Waypoints[i]):Lerp(CFrame.new(Waypoints[i + 1]), 0.5).Position, Waypoints[i + 1])
			Waypoint.Size       = Vector3.new(0.2, 0.2, (Waypoints[i + 1] - Waypoints[i]).Magnitude)
			Waypoint.Anchored   = true
			Waypoint.BrickColor = BrickColor.new("Really Red")
			Waypoint.Transparency = 0.5
			Waypoint.Material   = Enum.Material.Neon
			Waypoint.CanCollide = false
		end
	end

	function Pathfinder.ClearPath()
		if workspace:FindFirstChild("Path") then
			workspace.Path:ClearAllChildren()
		end
	end
	
	function Pathfind(Start, Destination, Radius, WaypointSpacing)
		-- local Path = PathfindingService:CreatePath(
		-- 	{
		-- 		WaypointSpacing = 4,
		-- 		AgentRadius     = 1,
		-- 		AgentHeight     = 5,
		-- 		AgentCanJump    = true
		-- 	}
		-- )

		-- if AgentHeight then
		--     Path = PathfindingService:CreatePath(
		-- 		{
		-- 			WaypointSpacing = 4,
		-- 			AgentRadius     = 1,
		-- 			AgentHeight     = AgentHeight,
		-- 			AgentCanJump    = true
		-- 		}
		-- 	)
		-- end

		-- local S = pcall(function()
		-- 	Path:ComputeAsync(Start, Destination)
		-- end)

		-- if S then
		-- 	if Path.Status ~= Enum.PathStatus.NoPath then
		-- 		local Waypoints = {}
		--         local Path      = Path:GetWaypoints()

		-- 		for i,v in pairs(Path) do
		--             Waypoints[#Waypoints + 1] = v.Position + NewVector3(0, 3, 0)
		-- 		end

		-- 		return Waypoints
		-- 	end
		-- end

		local Path = Pathfinder.FindPath(Start, Destination, Radius or 1, WaypointSpacing or 10)

		if Path then
			return Path
		else
			return nil
		end
	end

	function ReversePath(Path)
		local ReversedPath = {}

		for i = #Path, 1, -1 do
			ReversedPath[#ReversedPath + 1] = Path[i]
		end

		return ReversedPath
	end

	function IncreasePathHeight(Path)
		local NewPath = {}

		for i = 1, #Path do
			NewPath[#NewPath + 1] = Path[i] + NewVector3(0, 3, 0)
		end

		return NewPath
	end
end

do
	function TeleportPath(Path, StopCallback, FromNearestWaypoint, UsePathSpeed, Attempt)
		if Check() then
			WaitUntil(function()
				return not Check()
			end)
			return error()
		end

		for i,v in pairs(Path) do
			if type(v) ~= "vector" then
				Path[i] = v.p
			end
		end

		Attempt = Attempt or 0
		
		print(Attempt)

		if FromNearestWaypoint then
			local NewPath = {}
			local NearestWaypointIndex, NearestDistance = nil, 9e9

			for i,v in pairs(Path) do
				local Distance = (HumanoidRootPart.Position - v).Magnitude
				if Distance < NearestDistance then
					NearestWaypointIndex, NearestDistance = i, Distance
				end
			end

			for i = NearestWaypointIndex, #Path do
				NewPath[#NewPath + 1] = Path[i]
			end

			return TeleportPath(NewPath, StopCallback, nil, UsePathSpeed, Attempt)
		end

		Humanoid:SetStateEnabled("Seated", false)

		for i,v in pairs(Path) do
			if StopCallback and StopCallback(Path[i - 2], Path[i - 1]) then
				if StopCallback(Path[i - 2], Path[i - 1]) == "error" then
					return error()
				end
				break
			end

			if Check() then
				WaitUntil(function()
					return not Check()
				end)
				return error()
			end

			if Attempt >= 5 then
				Die()
				WaitForRespawn()

				LaggedBack = false

				return error()
			end

			if LaggedBack then
				wait(1)

				Attempt = Attempt + 1

				print(Attempt)
				
				local NewPath = {}
				local NearestWaypointIndex, NearestDistance = nil, 9e9

				for i,v in pairs(Path) do
					local Distance = (HumanoidRootPart.Position - v).Magnitude
					if Distance < NearestDistance then
						NearestWaypointIndex, NearestDistance = i, Distance
					end
				end

				for i = NearestWaypointIndex, #Path do
					NewPath[#NewPath + 1] = Path[i]
				end

				return TeleportPath(NewPath, StopCallback, FromNearestWaypoint, UsePathSpeed, Attempt)
			end

			if Humanoid.Sit and not Settings.AntiArrest then
				AttemptJump()
			end

			Teleport(NewCFrame(v), "Player", nil, nil, function()
				return StopCallback and StopCallback() or LaggedBack
			end, NewVector3(), (UsePathSpeed and Settings.GroundTpSpeed) or Settings.PlayerTpSpeed)
		end

		if not Settings.AntiArrest then
			Humanoid:SetStateEnabled("Seated", true)
		end
	end

	for i,v in pairs(CollectionService:GetTagged("Teleporter")) do
		if not Raycast(v:GetChildren()[2].Position, Sky) then
			table.insert(Teleporters, {
				Inside  = v:GetChildren()[1].Position,
				Outside = v:GetChildren()[2].Position
			})
		end
	end

	function GetNearestTeleporter(Position)
		Position = Position or (HumanoidRootPart and HumanoidRootPart.Position) or NewVector3(0, 0, 0)
		
		local NearestTeleporter, NearestDistance = nil, 9e9
		
		for i,v in pairs(Teleporters) do
			local Distance = DistanceXZ(v.Inside, Position)
			if Distance < NearestDistance then
				NearestTeleporter, NearestDistance = v, Distance
			end
		end
		
		return NearestTeleporter
	end

	function GetNearestExit()
		local NearestExit, NearestDistance = nil, 9e9

		for i,v in pairs(EscapeExits) do
			local Distance = DistanceXZ(HumanoidRootPart.Position, v)
			if Distance < NearestDistance then
				NearestExit, NearestDistance = v, Distance
			end
		end

		return NearestExit
	end

	function Escape_Alternative()
		if not Raycast(HumanoidRootPart.Position, Sky) then
			return
		end

		print(Raycast(HumanoidRootPart.Position, Sky).Instance:GetFullName())
		
		local RoofPosition = Raycast(ToSky(HumanoidRootPart.Position, Sky), Down).Position
		local Path = Pathfind(RoofPosition, HumanoidRootPart.Position)

		if Path then
			Path = ReversePath(Path)
			TeleportPath(Path, function(PreviousWaypoint, CurrentWaypoint)
				if CurrentWaypoint and not Raycast(CurrentWaypoint, Sky) then
					TeleportPath({
						CurrentWaypoint + ((CurrentWaypoint - PreviousWaypoint).Unit * 10)
					})
					return true
				end
			end, nil, true)

			wait(1)
		else
			SetStatus("Failed Trying Alternative Method. Retrying")
			Die()
			WaitForRespawn()
			return Escape()
		end
	end

	function Escape()
		wait()
		
		if Died then
			SetStatus("You Died. Waiting For Respawn")
			WaitForRespawn()
		end
		
		if CellTime.Visible or Inventory:FindFirstChild("Cuffed") then
			SetStatus("You've Been Arrested. Waiting To Be Released")
			WaitUntil(function()
				return not (CellTime.Visible or Inventory:FindFirstChild("Cuffed"))
			end)
			wait(2)
		end
		
		-- if (tostring(LocalPlayer.Team) == "Prisoner" or Raycast(HumanoidRootPart.Position, Sky)) and Settings.InstantEscape then
		-- 	local Teleporter  = GetNearestTeleporter()
		-- 	local Inside      = Teleporter.Inside
		-- 	local Outside     = Teleporter.Outside
		-- 	local Success     = false
		-- 	local Signal      = HumanoidRootPart:GetPropertyChangedSignal("CFrame"):Connect(function()
		-- 		if Distance(HumanoidRootPart.Position, Outside) < 10 then
		-- 			Success   = true
		-- 		end
		-- 	end)

		-- 	local Try = tick()
			
		-- 	while Success == false do
		-- 		if Check() then
		-- 			Signal:Disconnect()
		-- 			WaitUntil(function()
		-- 				return not Check()
		-- 			end)
		-- 			return error()
		-- 		end

		-- 		HumanoidRootPart.CFrame = NewCFrame(Inside)

		-- 		if tick() - Try > 3 then
		-- 			wait(3)
		-- 			Try = tick()
		-- 		else
		-- 			wait()
		-- 		end

		-- 		wait()
		-- 	end
			
		-- 	Signal:Disconnect()
		-- 	wait(1)

		-- 	return
		-- end
		
		if not Raycast(HumanoidRootPart.Position, Sky) then
			return
		end

		warn(Raycast(HumanoidRootPart.Position, Sky).Instance:GetFullName())

		SetStatus("Escaping")

		if DistanceXZ(HumanoidRootPart.Position, NewVector3(2238, 19, -2664)) < 300 and (not VehicleClass or VehicleClass == "Car") then
			local PathToCar = Pathfind(HumanoidRootPart.Position, NewVector3(2238, 19, -2664))

			if PathToCar then
				TeleportPath(PathToCar)

                local Car = nil

                if WaitUntil(function()
                    Car = GetNearestVehicle(nil, 60, true)
                    return Car
                end, 60, 0.1) then
                    Die()
                    WaitForRespawn()
                    return EnterVehicle(VehicleClass, Type)
                end

                while Car and Car:FindFirstChild("Seat") and Car.Seat.Player.Value == false do
                    for i,v in next, Specs do
                        if v.Part == Car.Seat then
                            v:Callback(true)
                            break
                        end
                    end
                    wait()
                end

                if Car and Car:FindFirstChild("Seat") and Car.Seat.PlayerName.Value == LocalPlayer.Name then
                    wait(0.5)
                
                    Teleport(NewCFrame(2272, 19, -2550) * CFrame.Angles(0, math.rad(10.13), 0), "Vehicle", "Direct")
                    Teleport(NewCFrame(2215, 21, -2467) * CFrame.Angles(0, math.rad(10.13), 0), "Vehicle", "Direct")
                    Teleport(NewCFrame(2286, 21, -2058) * CFrame.Angles(0, math.rad(10.13), 0), "Vehicle", "Direct")

                    wait(0.2)

                    return
                end
			end
		end

		local Exit;

		if DistanceXZ(HumanoidRootPart.Position, NewVector3(-1362, 19, -1731)) < 500 and HumanoidRootPart.Position.X < -1361 and HumanoidRootPart.Position.Z < -1659 then
			Exit = NewVector3(-1362, 19, -1731)

			if HumanoidRootPart.Position.Y < 10 then
				local Path = Pathfind(HumanoidRootPart.Position, NewVector3(-1483, -1, -1950))
				if not Path then
					Die()
					WaitForRespawn()
					return Escape()
				end
				TeleportPath(Path, nil, nil, true)
				TeleportPath({
					NewCFrame(-1484, 18, -1908),
					NewCFrame(-1484, 18, -1763),
					NewCFrame(-1454, 18, -1733)
				}, nil, nil, true)
			end
		elseif DistanceXZ(HumanoidRootPart.Position, NewVector3(-243, 18, 1614)) < 100 then
			Exit = NewVector3(-243, 18, 1614)
		else
			Exit = GetNearestExit()
		end

		if DistanceXZ(HumanoidRootPart.Position, Exit) > 500 then
			Die()
			WaitForRespawn()
			return Escape()
		end

		local Path = Pathfind(HumanoidRootPart.Position, Exit)
		if not Path then
			SetStatus("Failed Attempting To Escape. Trying Alternative Method")
			return Escape_Alternative()
		end

		TeleportPath(Path, nil, nil, true)
		wait(1)
	end

	function GetNearestVehicle(VehicleClass, MinimumDistance, IgnoreRoof)
		local NearestVehicle, NearestDistance = nil, MinimumDistance or 9e9

		for i,v in pairs(CollectionService:GetTagged("VehicleSeat")) do
			if not v:FindFirstChild("Player") then
				continue
			end
			
			local Vehicle          = v.Parent
			local Seat             = v
			local Blacklisted      = table.find(BlacklistedVehicles, Vehicle) ~= nil
			local Roof             = (IgnoreRoof and nil) or (not IgnoreRoof and Raycast(Seat.Position, Sky))
			local Engine           = Vehicle:FindFirstChild("Engine")
			local Locked           = Vehicle:GetAttribute("Locked")
			local VehicleClass     = CheckVehicle(Vehicle, VehicleClass)

			if Engine and not Blacklisted and not Roof and (GetLocalVehicleModel() == Vehicle or not Vehicle.Seat.Player.Value) and VehicleClass and (not Locked or Vehicle:FindFirstChild(LocalPlayer.Name)) then
				local Distance     = DistanceXZ(Seat.Position, HumanoidRootPart.Position)
				if NearestDistance > Distance then
					NearestVehicle, NearestDistance = Vehicle, Distance
				end
			end
		end

		return NearestVehicle
	end

	function GetNearestSpawn(SpecifiedSpawn)
		local NearestSpawn, NearestDistance = nil, 9e9

        for i,v in pairs(VehicleSpawns:GetChildren()) do
            if not v:FindFirstChild("Region") then
                continue
            end
            local Region           = v.Region
            local Blacklisted      = table.find(BlacklistedSpawns, Region)
            local Roof             = Raycast(Region.Position, Sky)
            local SpecifiedSpawn   = (SpecifiedSpawn == "Car" and table.find(Cars, v.Name)) or (SpecifiedSpawn == "Heli" and table.find(Helis, v.Name)) or (not SpecifiedSpawn and table.find(AllVehicles, v.Name))

            if not Blacklisted and not Roof and SpecifiedSpawn then
                local Distance     = DistanceXZ(Region.Position, HumanoidRootPart.Position)
                if NearestDistance > Distance then
                    NearestSpawn, NearestDistance = Region, Distance
                end
            end
        end
        if SpecifiedSpawn == "Heli" then
            for i, Region in pairs(HeliSpawns) do
                local Blacklisted      = table.find(BlacklistedSpawns, Region)
                local Roof             = Raycast(Region.Position, Sky)

                if not Blacklisted and not Roof then
                    local Distance     = DistanceXZ(Region.Position, HumanoidRootPart.Position)
                    if NearestDistance > Distance then
                        NearestSpawn, NearestDistance = Region, Distance
                    end
                end
            end
        end

		return NearestSpawn
	end

	function SpawnVehicle(VehicleType, VehicleMake)
		GarageSetUIOpen:FireServer(true)
		wait(0.1)
		SetThread(2)
		GarageUtils.onClickSpawnVehicle({
			vehicleType = VehicleType,
			vehicleMake = VehicleMake
		})
		SetThread(7)
	end

	function EnterVehicle(VehicleClass, Type)
		wait()

		local CurrentVehicle = GetLocalVehicleModel()

		if CurrentVehicle and CheckVehicle(CurrentVehicle, VehicleClass) then
            return
		end

		--EnteringCar = false

		if DistanceXZ(HumanoidRootPart.Position, NewVector3(2238, 19, -2664)) < 500 and (not VehicleClass or VehicleClass == "Car") then
			local PathToCar = Pathfind(HumanoidRootPart.Position, NewVector3(2238, 19, -2664))

			if PathToCar then
				TeleportPath(PathToCar)

                local Car = nil

                if WaitUntil(function()
                    Car = GetNearestVehicle(nil, 60, true)
                    return Car
                end, 60, 0.1) then
                    Die()
                    WaitForRespawn()
                    return EnterVehicle(VehicleClass, Type)
                end

				-- EnteringCar = true
				-- Humanoid.Sit = false

                while Car and Car:FindFirstChild("Seat") and Car.Seat.Player.Value == false do
                    for i,v in next, Specs do
                        if v.Part == Car.Seat then
                            v:Callback(true)
                            break
                        end
                    end
                    wait()
                end

                if Car and Car:FindFirstChild("Seat") and Car.Seat.PlayerName.Value == LocalPlayer.Name then
                    wait(0.5)
                
                    Teleport(NewCFrame(2272, 19, -2550) * CFrame.Angles(0, math.rad(10.13), 0), "Vehicle", "Direct")
                    Teleport(NewCFrame(2215, 21, -2467) * CFrame.Angles(0, math.rad(10.13), 0), "Vehicle", "Direct")
                    Teleport(NewCFrame(2286, 21, -2058) * CFrame.Angles(0, math.rad(10.13), 0), "Vehicle", "Direct")

                    wait(0.2)

                    return
                end
			end
		end
		
		local NearestVehicle        = GetNearestVehicle(VehicleClass)
		local NearestSpawn          = GetNearestSpawn(VehicleClass)

        if not NearestSpawn then
            SetStatus("Unexpected teleport error. Resetting")
            Die()
            WaitForRespawn()
            return error()
        end

		local NearestVehicleFarther = NearestVehicle and DistanceXZ(HumanoidRootPart.Position, NearestVehicle.Engine.Position) - 400 > DistanceXZ(HumanoidRootPart.Position, NearestSpawn.Position)
		local Start = tick()

		if not NearestVehicle or NearestVehicleFarther then
			NearestVehicle = nil

			if tostring(LocalPlayer.Team) ~= "Prisoner" and not Raycast(HumanoidRootPart.Position, NewVector3(0, 50, 0)) and DistanceXZ(HumanoidRootPart.Position, NearestSpawn.Position) > 200 and GetRemainingDebounce() < 0 and (not VehicleClass or VehicleClass == "Car") then
				if not Raycast(HumanoidRootPart.Position, NewVector3(0, -10, 0)) and Raycast(HumanoidRootPart.Position, NewVector3(0, -1000, 0)) then
					HumanoidRootPart.CFrame = NewCFrame(Raycast(HumanoidRootPart.Position, NewVector3(0, -1000, 0)).Position)
				end

                while true do
                    AttemptJump()
					
                    SpawnVehicle("Chassis", "Camaro")

                    WaitUntil(function()
                        return GetLocalVehicleModel() or not (tostring(LocalPlayer.Team) ~= "Prisoner" and Raycast(HumanoidRootPart.Position, NewVector3(0, -30, 0)) and not Raycast(HumanoidRootPart.Position, NewVector3(0, 50, 0))) or ((NotificationMessage.Text:find("spawn") or NotificationMessage.Text:find("something")) and NotificationGui.Enabled)
                    end, 5)

                    if GetLocalVehicleModel() and table.find(Cars, GetLocalVehicleModel().Name) then
                        return
                    end
                    if not (tostring(LocalPlayer.Team) ~= "Prisoner" and Raycast(HumanoidRootPart.Position, NewVector3(0, -30, 0)) and not Raycast(HumanoidRootPart.Position, NewVector3(0, 50, 0))) or ((NotificationMessage.Text:find("spawn") or NotificationMessage.Text:find("something")) and NotificationGui.Enabled) then
                        break
                    end

                    wait()
                end
			end

			local Waited = 0

			while NearestSpawn and not NearestVehicle and Waited <= 5 do
				if Distance(HumanoidRootPart.Position, NearestSpawn.Position) > 30 then
					Platform.CFrame           = NearestSpawn.CFrame + Vector3.new(0, -10, 0) + NearestSpawn.CFrame.RightVector * 20
					
					if VehicleClass == "Heli" then
						local CarSpawn          = GetNearestSpawn("Car")
						local CarSpawnNearer    = DistanceXZ(HumanoidRootPart.Position, CarSpawn.Position) + 400 < DistanceXZ(HumanoidRootPart.Position, NearestSpawn.Position)
						local Car               = GetNearestVehicle("Car")
						local CarNearer         = Car and DistanceXZ(HumanoidRootPart.Position, Car.Engine.Position) + 200 < DistanceXZ(HumanoidRootPart.Position, NearestSpawn.Position)

						print(GetLocalVehicleModel())

						if GetLocalVehicleModel() or CarNearer or CarSpawnNearer then
							Teleport(NearestSpawn.CFrame + Vector3.new(0, -5, 0) + NearestSpawn.CFrame.RightVector * 20, "Vehicle", "Sky", "Car", function()
								return GetLocalVehicleModel() and CheckVehicle(GetLocalVehicleModel(), VehicleClass)
							end)
                            wait(0.5)
							AttemptJump()
						else
							Teleport(NearestSpawn.CFrame + Vector3.new(0, -5, 0) + NearestSpawn.CFrame.RightVector * 20, "Player", "Sky", nil, function()
								return GetLocalVehicleModel() and CheckVehicle(GetLocalVehicleModel(), VehicleClass)
							end)
						end
					else
						Teleport(NearestSpawn.CFrame + Vector3.new(0, -5, 0) + NearestSpawn.CFrame.RightVector * 20, "Player", "Sky", nil, function()
                            return GetLocalVehicleModel() and CheckVehicle(GetLocalVehicleModel(), VehicleClass)
                        end)
					end
				end

				NearestVehicle = GetNearestVehicle(VehicleClass, 30)
				wait(0.1)
				Waited = Waited + 0.1
			end

			if not NearestSpawn then
				return EnterVehicle(VehicleClass, Type)
			end

			if Waited >= 5 then
				BlacklistedSpawns[#BlacklistedSpawns + 1] = NearestSpawn
		
				delay(30, function()
					table.remove(BlacklistedSpawns, table.find(BlacklistedSpawns, NearestSpawn))
				end)
		
				return EnterVehicle(VehicleClass, Type)
			end
		end

		if tostring(LocalPlayer.Team) ~= "Prisoner" and not Raycast(HumanoidRootPart.Position, NewVector3(0, 50, 0)) and DistanceXZ(HumanoidRootPart.Position, NearestVehicle.Engine.Position) > 200 and GetRemainingDebounce() < 0 and (not VehicleClass or VehicleClass == "Car") then
			if not Raycast(HumanoidRootPart.Position, NewVector3(0, -10, 0)) and Raycast(HumanoidRootPart.Position, NewVector3(0, -1000, 0)) then
				HumanoidRootPart.CFrame = NewCFrame(Raycast(HumanoidRootPart.Position, NewVector3(0, -1000, 0)).Position)
			end

			while true do
				AttemptJump()
				
				SpawnVehicle("Chassis", "Camaro")

				WaitUntil(function()
					return GetLocalVehicleModel() or not (tostring(LocalPlayer.Team) ~= "Prisoner" and Raycast(HumanoidRootPart.Position, NewVector3(0, -30, 0)) and not Raycast(HumanoidRootPart.Position, NewVector3(0, 50, 0))) or ((NotificationMessage.Text:find("spawn") or NotificationMessage.Text:find("something")) and NotificationGui.Enabled)
				end, 5)

				if GetLocalVehicleModel() and table.find(Cars, GetLocalVehicleModel().Name) then
					return
				end
				if not (tostring(LocalPlayer.Team) ~= "Prisoner" and Raycast(HumanoidRootPart.Position, NewVector3(0, -30, 0)) and not Raycast(HumanoidRootPart.Position, NewVector3(0, 50, 0))) or ((NotificationMessage.Text:find("spawn") or NotificationMessage.Text:find("something")) and NotificationGui.Enabled) then
					break
				end

				wait()
			end
		end

		while (not GetLocalVehicleModel() or not CheckVehicle(GetLocalVehicleModel(), VehicleClass)) and NearestVehicle and NearestVehicle:FindFirstChild("Seat") and NearestVehicle.Seat.Player.Value == false and not table.find(BlacklistedVehicles, NearestVehicle) do
			if Distance(HumanoidRootPart.Position, NearestVehicle.Seat.Position) > 30 then
				if VehicleClass == "Heli" then
                    local CarSpawn       = GetNearestSpawn("Car")
                    local CarSpawnNearer = DistanceXZ(HumanoidRootPart.Position, CarSpawn.Position) + 400 < DistanceXZ(HumanoidRootPart.Position, NearestVehicle.Seat.Position)
                    local Car            = GetNearestVehicle("Car")
                    local CarNearer      = Car and DistanceXZ(HumanoidRootPart.Position, Car.Engine.Position) + 200 < DistanceXZ(HumanoidRootPart.Position, NearestVehicle.Seat.Position)

					print(GetLocalVehicleModel())

                    if GetLocalVehicleModel() or CarNearer or CarSpawnNearer then
						Platform.CFrame = NearestVehicle.Seat.CFrame + NearestVehicle.Seat.CFrame.RightVector * 20

						Teleport(NearestVehicle.Seat.CFrame + Vector3.new(0, 5, 0) + NearestVehicle.Seat.CFrame.RightVector * 20, "Vehicle", "Sky", "Car", function()
                            return not NearestVehicle or not NearestVehicle:FindFirstChild("Seat") or NearestVehicle.Seat.Player.Value
                        end)

                        AttemptJump()

                        if NearestVehicle and NearestVehicle:FindFirstChild("Seat") then
                            Teleport(NearestVehicle.Seat.CFrame + Vector3.new(0, 5, 0), "Player", "Sky", nil, function()
                                return not NearestVehicle or not NearestVehicle:FindFirstChild("Seat") or NearestVehicle.Seat.Player.Value
                            end)
                        end
					else
						Teleport(NearestVehicle.Seat.CFrame + Vector3.new(0, 5, 0), "Player", "Sky", nil, function()
							return not NearestVehicle or not NearestVehicle:FindFirstChild("Seat") or NearestVehicle.Seat.Player.Value
						end)
					end
				else
					Teleport(NearestVehicle.Seat.CFrame + Vector3.new(0, 5, 0), "Player", "Sky", nil, function()
                        return not NearestVehicle or not NearestVehicle:FindFirstChild("Seat") or NearestVehicle.Seat.Player.Value
                    end)
				end
			end

			if not NearestVehicle or not NearestVehicle:FindFirstChild("Seat") then
				return EnterVehicle(VehicleClass, Type)
			end

			-- EnteringCar = true
			-- Humanoid.Sit = false

			for i,v in pairs(Specs) do
				if v.Part == NearestVehicle.Seat then
					v:Callback(true)
					break
				end
			end

			if NotificationMessage.Text:find("Cannot use vehicle here") and NotificationGui.Enabled then
				NotificationGui.Enabled = false
				table.insert(BlacklistedVehicles, NearestVehicle)
				return EnterVehicle(VehicleClass, Type)
			end

			if NearestVehicle:GetAttribute("Locked") and not NearestVehicle:FindFirstChild(LocalPlayer.Name) then
				table.insert(BlacklistedVehicles, NearestVehicle)
				return EnterVehicle(VehicleClass, Type)
			end

			wait()
		end
		
		if not NearestVehicle or not NearestVehicle:FindFirstChild("Seat") or table.find(BlacklistedVehicles, NearestVehicle) or NearestVehicle.Seat.PlayerName.Value ~= LocalPlayer.Name then
			return EnterVehicle(VehicleClass, Type)
		end

		local CurrentVehicle = GetLocalVehicleModel()
		
        if not CurrentVehicle or not CheckVehicle(CurrentVehicle, VehicleClass) then
			return EnterVehicle(VehicleClass, Type)
		end

		-- EnteringCar = false
	end

    function CheckVehicle(CurrentVehicle, VehicleClass)
        if not CurrentVehicle then
            return false
        end

        return (VehicleClass == "Car" and table.find(Cars, CurrentVehicle.Name))
            or (VehicleClass == "Heli" and table.find(Helis, CurrentVehicle.Name))
            or (not VehicleClass and table.find(AllVehicles, CurrentVehicle.Name))
    end

	function Teleport_V2(CF, Mode, Type, VehicleClass, StopCallback, Direction, CustomSpeed)
		Mode = Mode or "Player"
        Type = Type or (Mode == "Player" and "Direct" or "Sky")

        if StopCallback and StopCallback() then
            if StopCallback() == "error" then
                return error()
            end
            return
        end
        if Died then
            return error()
        end

		for i,v in pairs(SteppedSignals) do
			v:Disconnect()
		end

        local Root
        local Start
        local End
        local Speed
        local LagbackCount = 0
        local CurrentCharacter = Character
		local CollisionStore = {}
        local Sounds = {}

        if Mode == "Player" then
            Root = HumanoidRootPart
            Speed = Settings.PlayerTpSpeed or DefaultSettings.PlayerTpSpeed
            SteppedSignals["Noclip"] = RunService.Stepped:Connect(function()
                if CurrentCharacter and CurrentCharacter.Parent then
                    for i,v in pairs(CurrentCharacter:GetDescendants()) do
                        if v:IsA("BasePart") then
                            v.CanCollide = false
                        end
                    end
                else
                    SteppedSignals["Noclip"]:Disconnect()
                end
            end)
        elseif Mode == "Vehicle" then
            if not GetLocalVehicleModel() or not CheckVehicle(GetLocalVehicleModel(), VehicleClass) then
                EnterVehicle(VehicleClass)
            end

            local CurrentVehicle = GetLocalVehicleModel()

            Root = CurrentVehicle.PrimaryPart
            Speed = Settings.VehicleTpSpeed or DefaultSettings.VehicleTpSpeed

            if Type == "Instant" then
                local Try = tick()
    
                while GetLocalVehicleModel() do
                    if StopCallback and StopCallback() then
                        if StopCallback() == "error" then
                            return error()
                        end
                        return
                    end
                    
                    Root.CFrame = NewCFrame(type(CF) == "function" and CF().p or CF.p)
                    
                    if tick() - Try > 3 then
                        wait(1)
                        Try = tick()
                    else
                        wait()
                    end
                end
    
                CurrentVehicle.Parent = nil
    
                return
            end

            for i,v in pairs(Root:GetChildren()) do
				if v.ClassName == "Sound" then
					Sounds[#Sounds + 1] = v
					v.Parent = nil
				end
			end
			for i,v in pairs(CurrentVehicle:GetDescendants()) do
				if v:IsA("BasePart") then
					CollisionStore[v] = v.CanCollide
					v.CanCollide = false
				end
			end
        end

        if Type == "Direct" then
            Start = Root.Position + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
            End   = (type(CF) == "function" and CF().p or CF.p) + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
        elseif Type == "Sky" then
            Escape()

            Start = ToSky(Root.Position, 500)
            End   = ToSky(type(CF) == "function" and CF().p or CF.p, 500)
        end

        local BV = Instance.new("BodyVelocity", Root)
        BV.Velocity = NewVector3()
        BV.MaxForce = NewVector3(9e9, 9e9, 9e9)
        
        if Mode == "Vehicle" and GetLocalVehicleModel() and table.find(Helis, GetLocalVehicleModel().Name) then
            BV.Parent = GetLocalVehicleModel().Model.TopDisc
        end

        Root.CFrame = NewCFrame(Start)
		LaggedBack = false

        while Distance(Root.Position, End) > 2 do
            if Distance(Root.Position, End) < (Mode == "Vehicle" and 10 or 5) and type(CF) ~= "function" then
                Speed = (Mode == "Vehicle" and 100 or math.min(Speed, 40))
            end
            if (StopCallback and StopCallback()) or (Mode == "Vehicle" and (not GetLocalVehicleModel() or not BV.Parent:IsDescendantOf(GetLocalVehicleModel()))) or (Mode == "Player" and (Root ~= HumanoidRootPart or BV.Parent ~= HumanoidRootPart)) or Died or LagbackCount >= 10 then
                break
            end
            if Mode == "Player" then
                if Humanoid.Sit and not Settings.AntiArrest then
                    AttemptJump()
                end
            end
            if Type == "Sky" and Root.Position.Y < 400 then
				LagbackCount = LagbackCount + 1
                LaggedBack = false
                BV.Velocity = NewVector3()

				print("LAGGG 1!!!", LagbackCount)
                wait(1)

                Root.CFrame = NewCFrame(ToSky(Root.Position, 500))
            end
            if LaggedBack then
                LagbackCount = LagbackCount + 1
                LaggedBack = false
                BV.Velocity = NewVector3()
                
				print("LAGGG 2!!!", LagbackCount)
                wait(1)
            end
			if type(CF) == "function" then
				if Type == "Direct" then
					End = (type(CF) == "function" and CF().p or CF.p.p) + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
				elseif Type == "Sky" then
					End = ToSky(type(CF) == "function" and CF().p or CF.p, 500)
				end
			end

            BV.Velocity = (End - Root.Position).Unit * (CustomSpeed or Speed)

            wait()
        end

        if Mode == "Player" then
            SteppedSignals["Noclip"]:Disconnect()

        	if Root ~= HumanoidRootPart or BV.Parent ~= HumanoidRootPart then
	            return error()
	        end
		elseif Mode == "Vehicle" and GetLocalVehicleModel() then
            for i,v in pairs(Sounds) do
				v.Parent = Root
			end
			for i,v in pairs(GetLocalVehicleModel():GetDescendants()) do
				if v:IsA("BasePart") then
					v.CanCollide = CollisionStore[v]
				end
			end

			if not BV.Parent:IsDescendantOf(GetLocalVehicleModel()) then
				return error()
			end
		end

        BV.Velocity = NewVector3()
        BV:Destroy()
		
        if StopCallback and StopCallback() then
            if StopCallback() == "error" then
                return error()
            end
            return
        end
        if Died then
            return error()
        end
        if LagbackCount >= 5 then
            Die()
            return error()
        end

        if (Mode == "Vehicle" and not GetLocalVehicleModel()) then
            return Teleport(CF, Mode, Type, VehicleClass, StopCallback, Direction, CustomSpeed)
        end
		
        Root.CFrame = type(CF) == "function" and CF() or CF
        Root.Velocity = NewVector3()
	end

	function Teleport_Tween(CF, Mode, Type, VehicleClass, StopCallback, Direction, CustomSpeed)
		Mode = Mode or "Player"
        Type = Type or (Mode == "Player" and "Direct" or "Sky")

        if StopCallback and StopCallback() then
            if StopCallback() == "error" then
                return error()
            end
            return
        end
        if Died then
            return error()
        end

		for i,v in pairs(SteppedSignals) do
			v:Disconnect()
		end

        local Root
        local Start
        local End
        local Speed
		local CheckLagback
        local LagbackCount = 0
        local CurrentCharacter = Character
		local CollisionStore = {}

        if Mode == "Player" then
            Root = HumanoidRootPart
            Speed = Settings.PlayerTpSpeed or DefaultSettings.PlayerTpSpeed
            SteppedSignals["Noclip"] = RunService.Stepped:Connect(function()
                if CurrentCharacter and CurrentCharacter.Parent then
                    for i,v in pairs(CurrentCharacter:GetDescendants()) do
                        if v:IsA("BasePart") then
                            v.CanCollide = false
                        end
                    end
                else
                    SteppedSignals["Noclip"]:Disconnect()
                end
            end)
        elseif Mode == "Vehicle" then
            if not GetLocalVehicleModel() or not CheckVehicle(GetLocalVehicleModel(), VehicleClass) then
                EnterVehicle(VehicleClass)
            end

            local CurrentVehicle = GetLocalVehicleModel()

            Root = CurrentVehicle.PrimaryPart
            Speed = Settings.VehicleTpSpeed or DefaultSettings.VehicleTpSpeed

			CheckLagback = LagBackCheck(Root, 60)

            if Type == "Instant" then
                local Try = tick()
    
                while GetLocalVehicleModel() do
                    if StopCallback and StopCallback() then
                        if StopCallback() == "error" then
                            return error()
                        end
                        return
                    end
                    
                    Root.CFrame = NewCFrame(type(CF) == "function" and CF().p or CF.p)
                    
                    if tick() - Try > 3 then
                        wait(1)
                        Try = tick()
                    else
                        wait()
                    end
                end
    
                CurrentVehicle.Parent = nil
    
                return
            end

			for i,v in pairs(CurrentVehicle:GetDescendants()) do
				if v:IsA("BasePart") then
					CollisionStore[v] = v.CanCollide
					v.CanCollide = false
				end
			end
        end

        if Type == "Direct" then
            Start = Root.Position + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
            End   = (type(CF) == "function" and CF().p or CF.p) + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
        elseif Type == "Sky" then
            Escape()

            Start = ToSky(Root.Position, 500)
            End   = ToSky(type(CF) == "function" and CF().p or CF.p, 500)
        end

        local BV = Instance.new("BodyVelocity", Root)
        BV.Velocity = NewVector3()
        BV.MaxForce = NewVector3(9e9, 9e9, 9e9)
        
        if Mode == "Vehicle" and GetLocalVehicleModel() and table.find(Helis, GetLocalVehicleModel().Name) then
            BV.Parent = GetLocalVehicleModel().Model.TopDisc
        end

        Root.CFrame = NewCFrame(Start)
		LaggedBack = false

        while Distance(Root.Position, End) > (Mode == "Vehicle" and 10 or 5) do
            if (StopCallback and StopCallback()) or (Mode == "Vehicle" and (not GetLocalVehicleModel() or not BV.Parent:IsDescendantOf(GetLocalVehicleModel()))) or (Mode == "Player" and (Root ~= HumanoidRootPart or BV.Parent ~= HumanoidRootPart)) or Died or LagbackCount >= 5 then
                break
            end
            if Mode == "Player" then
                if Humanoid.Sit and not Settings.AntiArrest then
                    AttemptJump()
                end
            end
			if Type == "Sky" and Root.Position.Y < 400 then
				LagbackCount = LagbackCount + 1
                LaggedBack = false

				print("LAGGG 1!!!", LagbackCount)
                wait(1)

                Root.CFrame = NewCFrame(ToSky(Root.Position, 500))
            end
            if LaggedBack then
                LagbackCount = LagbackCount + 1
                LaggedBack = false
                
				print("LAGGG 2!!!", LagbackCount)
                wait(1)
            end
			if type(CF) == "function" then
				if Type == "Direct" then
					End = (type(CF) == "function" and CF().p or CF.p.p) + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
				elseif Type == "Sky" then
					End = ToSky(type(CF) == "function" and CF().p or CF.p, 500)
				end
			end

			local NextDirection = Root.Position + ((End - Root.Position).Unit * math.min(Distance(Root.Position, End), Mode == "Vehicle" and 60 or 10))
			local Tween = TweenService:Create(Root, TweenInfo.new(Distance(Root.Position, NextDirection) / (CustomSpeed or Speed), Enum.EasingStyle.Linear), {
				CFrame = NewCFrame(NextDirection)
			})
            Tween:Play()
			Tween.Completed:Wait()
        end

		if CheckLagback then
			CheckLagback:Stop()
		end

        if Mode == "Player" then
            SteppedSignals["Noclip"]:Disconnect()

        	if Root ~= HumanoidRootPart or BV.Parent ~= HumanoidRootPart then
	            return error()
	        end
		elseif Mode == "Vehicle" and GetLocalVehicleModel() then
			for i,v in pairs(GetLocalVehicleModel():GetDescendants()) do
				if v:IsA("BasePart") then
					v.CanCollide = CollisionStore[v]
				end
			end

			if not BV.Parent:IsDescendantOf(GetLocalVehicleModel()) then
				return error()
			end
		end

        BV.Velocity = NewVector3()
        BV:Destroy()
		
        if StopCallback and StopCallback() then
            if StopCallback() == "error" then
                return error()
            end
            return
        end
        if Died then
            return error()
        end
        if LagbackCount >= 5 then
            Die()
            return error()
        end

        if (Mode == "Vehicle" and not GetLocalVehicleModel()) then
            return Teleport(CF, Mode, Type, VehicleClass, StopCallback, Direction, CustomSpeed)
        end

        Root.CFrame = type(CF) == "function" and CF() or CF
        Root.Velocity = NewVector3()
	end

	function Teleport_V1(CF, Mode, Type, VehicleClass, StopCallback, Direction, CustomSpeed)
		Mode = Mode or "Player"
        Type = Type or (Mode == "Player" and "Direct" or "Sky")

        if StopCallback and StopCallback() then
            if StopCallback() == "error" then
                return error()
            end
            return
        end
        if Died then
            return error()
        end

		for i,v in pairs(SteppedSignals) do
			v:Disconnect()
		end

        local Root
        local Start
        local End
        local Speed
		local CheckLagback
        local LagbackCount = 0
        local CurrentCharacter = Character
		local CollisionStore = {}

        if Mode == "Player" then
            Root = HumanoidRootPart
            Speed = Settings.PlayerTpSpeed or DefaultSettings.PlayerTpSpeed
            SteppedSignals["Noclip"] = RunService.Stepped:Connect(function()
                if CurrentCharacter and CurrentCharacter.Parent then
                    for i,v in pairs(CurrentCharacter:GetDescendants()) do
                        if v:IsA("BasePart") then
                            v.CanCollide = false
                        end
                    end
                else
                    SteppedSignals["Noclip"]:Disconnect()
                end
            end)
        elseif Mode == "Vehicle" then
            if not GetLocalVehicleModel() or not CheckVehicle(GetLocalVehicleModel(), VehicleClass) then
                EnterVehicle(VehicleClass)
            end

            local CurrentVehicle = GetLocalVehicleModel()

            Root = CurrentVehicle.PrimaryPart
            Speed = Settings.VehicleTpSpeed or DefaultSettings.VehicleTpSpeed

			CheckLagback = LagBackCheck(Root, (Speed >= 200 and 11 + (((Speed - 200) / 400) * 8) or 2 + (((Speed - 16) / 134) * 3)))

            if Type == "Instant" then
                local Try = tick()
    
                while GetLocalVehicleModel() do
                    if StopCallback and StopCallback() then
                        if StopCallback() == "error" then
                            return error()
                        end
                        return
                    end
                    
                    Root.CFrame = NewCFrame(type(CF) == "function" and CF().p or CF.p)
                    
                    if tick() - Try > 3 then
                        wait(1)
                        Try = tick()
                    else
                        wait()
                    end
                end
    
                CurrentVehicle.Parent = nil
    
                return
            end

			for i,v in pairs(CurrentVehicle:GetDescendants()) do
				if v:IsA("BasePart") then
					CollisionStore[v] = v.CanCollide
					v.CanCollide = false
				end
			end
        end

        if Type == "Direct" then
            Start = Root.Position + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
            End   = (type(CF) == "function" and CF().p or CF.p) + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
        elseif Type == "Sky" then
            Escape()

            Start = ToSky(Root.Position, 500)
            End   = ToSky(type(CF) == "function" and CF().p or CF.p, 500)
        end

        local BV = Instance.new("BodyVelocity", Root)
        BV.Velocity = NewVector3()
        BV.MaxForce = NewVector3(9e9, 9e9, 9e9)
        
        if Mode == "Vehicle" and GetLocalVehicleModel() and table.find(Helis, GetLocalVehicleModel().Name) then
            BV.Parent = GetLocalVehicleModel().Model.TopDisc
        end

        Root.CFrame = NewCFrame(Start)
		LaggedBack = false

        while Distance(Root.Position, End) > (Mode == "Vehicle" and 18 or 4) do
            if (StopCallback and StopCallback()) or (Mode == "Vehicle" and (not GetLocalVehicleModel() or not BV.Parent:IsDescendantOf(GetLocalVehicleModel()))) or (Mode == "Player" and (Root ~= HumanoidRootPart or BV.Parent ~= HumanoidRootPart)) or Died or LagbackCount >= 5 then
                break
            end
            if Mode == "Player" then
                if Humanoid.Sit and not Settings.AntiArrest then
                    AttemptJump()
                end
            end
            if Type == "Sky" and Root.Position.Y < 400 then
				LagbackCount = LagbackCount + 1
                LaggedBack = false

				print("LAGGG 1!!!", LagbackCount)
                wait(1)

                Root.CFrame = NewCFrame(ToSky(Root.Position, 500))
            end
            if LaggedBack then
                LagbackCount = LagbackCount + 1
                LaggedBack = false
                
				print("LAGGG 2!!!", LagbackCount)
                wait(1)
            end
			if type(CF) == "function" then
				if Type == "Direct" then
					End = (type(CF) == "function" and CF().p or CF.p.p) + (Direction or (Mode == "Vehicle" and NewVector3(0, 5, 0) or NewVector3()))
				elseif Type == "Sky" then
					End = ToSky(type(CF) == "function" and CF().p or CF.p, 500)
				end
			end

			Root.CFrame = Root.CFrame + (End - Root.Position).Unit * (Speed >= 200 and 10 + (((Speed - 200) / 400) * 8) or 1 + (((Speed - 16) / 134) * 3))

			task.wait()
        end

		if CheckLagback then
			CheckLagback:Stop()
		end

        if Mode == "Player" then
            SteppedSignals["Noclip"]:Disconnect()

        	if Root ~= HumanoidRootPart or BV.Parent ~= HumanoidRootPart then
	            return error()
	        end
		elseif Mode == "Vehicle" and GetLocalVehicleModel() then
			for i,v in pairs(GetLocalVehicleModel():GetDescendants()) do
				if v:IsA("BasePart") then
					v.CanCollide = CollisionStore[v]
				end
			end

			if not BV.Parent:IsDescendantOf(GetLocalVehicleModel()) then
				return error()
			end
		end

        BV.Velocity = NewVector3()
        BV:Destroy()

		task.wait()
		
        if StopCallback and StopCallback() then
            if StopCallback() == "error" then
                return error()
            end
            return
        end
        if Died then
            return error()
        end
        if LagbackCount >= 5 then
            Die()
            return error()
        end

        if (Mode == "Vehicle" and not GetLocalVehicleModel()) then
            return Teleport(CF, Mode, Type, VehicleClass, StopCallback, Direction, CustomSpeed)
        end
		
        Root.CFrame = type(CF) == "function" and CF() or CF
		Root.Velocity = NewVector3()
	end

	function Teleport(...)
		return (({
			["V2"] = Teleport_V2,
			["V1"] = Teleport_V1,
			["Tween"] = Teleport_Tween
		})[Settings.TeleportMethod] or Teleport_V2)(...)
	end
end

--[[ Auto Rob Utilities ]]
--// For Testing

if JB_DEBUG then
	warn("[Jailbreaker Debugging]: Loading Utilities Functions..")
end

local Last = nil
local SecondElapsed = nil

if getgenv().V2_ServerHop then
	Last = getgenv().Last
	SecondElapsed = getgenv().SecondElapsed
end

do
    function OpenSafe()

    end

    function BypassTp()
        HumanoidRootPart.Parent = nil
        HumanoidRootPart.Parent = Character
    end

    function InstantTp(CF)
        BypassTp()
        HumanoidRootPart.CFrame = CF
    end

    function CallPlaneFunc()
        if not CallPlaneCallback then
            return
        end

        CallPlaneCallback(nil, true)
    end

    function CopEntered()
        return Settings.BankEscapePoliceEntered and ("The police have entered the building!"):sub(1, 10) == (NotificationMessage.Text):sub(1, 10)
    end

    function secondToTimeFormat(second)
        local seconds = tostring(second % 60)
        local minutes = tostring(math.floor(second / 60) % 60)
        local hours   = tostring(math.floor(math.floor(second / 60) / 60) % 60)
        local days    = tostring(math.floor(math.floor(math.floor(second / 60) / 60) / 24))

        seconds = string.rep('0', 2 - #seconds)..seconds
        minutes = string.rep('0', 2 - #minutes)..minutes
        hours   = string.rep('0', 2 - #hours)..hours
        days    = string.rep('0', 2 - #days)..days

        return string.format(("%sd:%sh:%sm:%ss"), days, hours, minutes, seconds)
    end


    function GetCashEarned()
        return LocalPlayer.leaderstats.Money.Value - (Last or LocalPlayer.leaderstats.Money.Value)
    end

    function GetTimeElapsed()
        return secondToTimeFormat(SecondElapsed or 0)
    end

    function GetEstimated()
        return MoneyPerHour(LocalPlayer.leaderstats.Money.Value - (Last or LocalPlayer.leaderstats.Money.Value), SecondElapsed or 0)
    end

    function SetEstimated(Amount)
    end

    function SetEarned(Earned)
    end

    function SetTime(Time)
    end

    local Tasks = {}
    
    RunService.Stepped:Connect(function(_, dt)
        for _, task in pairs(Tasks) do
            task.time = task.time + dt
            if task.time >= task.second then
                task.time = task.time - task.second
                task.func(function()
					table.remove(Tasks, _)
				end)
            end
        end
    end)

    function ForEvery(Second, Task)
        table.insert(Tasks, {
            time = Second,
            second = Second,
            func = Task
        })
    end

    function CheckPlaneCrates()
        if not workspace:FindFirstChild("Plane") or not workspace.Plane:FindFirstChild("Crates") then
            return false
        end

        for i,v in pairs(PlaneCrates) do
            if workspace.Plane.Crates:FindFirstChild(v) and workspace.Plane.Crates:FindFirstChild(v)['1'].Transparency < 1 then
                return true
            end
        end

        return false
    end

    function GetCargoTrainBoxCar()
        for i,v in pairs(CargoTrainBoxCars) do
            if Trains:FindFirstChild(v) then
                return Trains:FindFirstChild(v)
            end
        end
    end

    function BagVisible()
        return PlayerGui:FindFirstChild("PowerPlantRobberyGui") or PlayerGui.RobberyMoneyGui.Enabled
    end

    function BagFull()
        if PlayerGui:FindFirstChild("PowerPlantRobberyGui") then
            return true
        end
        if PlayerGui.RobberyMoneyGui.Enabled == false then
            return false
        end
        local Moneys = string.split(PlayerGui.RobberyMoneyGui.Container.Bottom.Progress.Amount.Text, " / ")

        return (Moneys[1] == Moneys[2]) or tonumber(Moneys[1]:match("%d+")) >= (Settings.BagSellValue or 999999)
    end

    function CheckUranium()
        local PowerPlantRobberyGui = PlayerGui:FindFirstChild("PowerPlantRobberyGui")

        if not PowerPlantRobberyGui then
            return 0
        end

        local Price                = PowerPlantRobberyGui.Price

        return tonumber(Price.TextLabel.Text:gsub(",", ""):match("Uranium Value: $(%d+)"))
    end

    function AttemptSell(BagType)
        Platform.CFrame = NewCFrame(0, 0, 0)
        
        if BagType == "CargoPlane" then
            SetStatus("Going To Cargo Port")
            Teleport(NewCFrame(-324, 21, 2041) * CFrame.Angles(0, math.rad(36), 0), "Vehicle")

            SetStatus("Waiting")
            wait(Settings.PlaneWaitBeforeSell or 5)

            SetStatus("Selling")
			AttemptJump()
			wait(0.1)
            Teleport(NewCFrame(-342, 21, 2053))

            WaitUntil(function()
                return not BagVisible()
            end, 5)
        elseif BagType == "Jewelry" then
            SetStatus("Going To Criminal Base")
            Teleport(NewCFrame(-220, 18, 1624), "Vehicle")
            SetStatus("Selling")
            WaitUntil(function()
                return not BagVisible()
            end, 5)
        else
            local VolcanoPath = {
                {
                    NewCFrame(2293, 21, -2018) * CFrame.Angles(0, math.rad(10.13), 0),
                    NewCFrame(2215, 21, -2467) * CFrame.Angles(0, math.rad(10.13), 0)
                },
                {
                    NewCFrame(2031, 21, -3206) * CFrame.Angles(0, math.rad(213), 0),
                    NewCFrame(2108, 21, -3073) * CFrame.Angles(0, math.rad(189.3), 0),
                    NewCFrame(2176, 21, -2687) * CFrame.Angles(0, math.rad(189.3), 0)
                }
            }

            table.sort(VolcanoPath, function(a, b)
                return DistanceXZ(HumanoidRootPart.Position, a[1].p) < Distance(HumanoidRootPart.Position, b[1].p)
            end)

            local Path = VolcanoPath[1]

            SetStatus("Going To Volcano Base")

            Teleport(Path[1], "Vehicle", "Sky", nil, function()
                if not BagVisible() then
                    return "error"
                end
            end)

			wait(0.3)

            for i = 2, #Path do
                Teleport(Path[i], "Vehicle", "Direct")
            end

            if BagType == "PowerPlant" and PlayerGui:FindFirstChild("PowerPlantRobberyGui") then
                if CheckUranium() > Settings.PowerPlantUraniumValue then
                    SetStatus("Waiting For Uranuim Value To Reach $".. tostring(Settings.PowerPlantUraniumValue or 5700))
                    repeat wait() until CheckUranium() <= (Settings.PowerPlantUraniumValue or 5700)
                end
            end

            SetStatus("Selling")

            if BagType ~= "Casino" then
                Teleport(NewCFrame(2288, 21, -2584), "Vehicle", "Direct")
            end

            WaitUntil(function()
                return not BagVisible()
            end, 5)

            for i = #Path, 1, -1 do
                Teleport(Path[i], "Vehicle", "Direct")
            end

            wait(0.3)
        end

        if BagVisible() then
            return AttemptSell(BagType)
        end
    end

    function Safety()
        if Died then
            return
        end

        local Root = GetLocalVehicleModel() and GetLocalVehicleModel().PrimaryPart or HumanoidRootPart

        Platform.CFrame = NewCFrame(ToSky(Root.Position, 100000))
        Root.CFrame     = NewCFrame(ToSky(Root.Position, 100005))
    end

    function Cooldown()
        Settings.Cooldown = Settings.Cooldown or 0
        if Settings.Cooldown == 0 then
            return
        end

        Safety()

        for i = Settings.Cooldown, 1, -1 do
            SetStatus(("Cooldown (%d)"):format(i))
            wait(1)
        end

        SetStatus(("Cooldown (%d)"):format(0))

        wait(0.5)
    end

    function GetNearestAirdrop()
        if Died then
            return
        end

        -- local NearestAirdrop, NearestDistance = nil, 9e9

        -- for i,v in pairs(CollectionService:GetTagged("Briefcase")) do
        --     local Landed    = v:GetAttribute("BriefcaseLanded")
        --     local Collected = v:GetAttribute("BriefcaseCollected")

        --     if v:FindFirstChild("Root") and Landed and Collected == false then
        --         local Distance = DistanceXZ(HumanoidRootPart.Position, v.Root.Position)
        --         if Distance < NearestDistance then
        --             NearestAirdrop, NearestDistance = v, Distance
        --         end
        --     end
        -- end

        -- return NearestAirdrop

        local NearestAirdrop, NearestDistance = nil, 9e9

        for i,v in pairs(CollectionService:GetTagged("Briefcase")) do
            print(v)

            RaycastIgnoreList[#RaycastIgnoreList + 1] = v
            
            local Collected = v:GetAttribute("BriefcaseCollected")

            if v:FindFirstChild("Root") and Collected == false then
                local Distance = DistanceXZ(HumanoidRootPart.Position, v.Root.Position)
                if Distance < NearestDistance then
                    NearestAirdrop, NearestDistance = v, Distance
                end
            end
        end

        return NearestAirdrop
    end

    function GetNearestPlayer(MinimumDistance)
        if Died then
            return
        end

        -- Mansion Boss Is A NPC Not Player :(
        -- if MansionRobbery:FindFirstChild("ActiveBoss") then
        --     if MansionRobbery.ActiveBoss:FindFirstChild("Head") and DistanceXZ(MansionRobbery.ActiveBoss.HumanoidRootPart.Position, HumanoidRootPart.Position).Magnitude < 250 and MansionRobbery.ActiveBoss.Humanoid.Health > 1 then
        --         return {Character = MansionRobbery.ActiveBoss}
        --     end
        -- end

        local NearestPlayer, NearestDistance = nil, (MinimumDistance or Settings.KillAuraRange or 100)
        local CurrentTeam = tostring(LocalPlayer.Team)

        for i,v in pairs(Players:GetPlayers()) do
            local PlayerTeam = tostring(v.Team)
            local Excluded   = table.find(Settings.KillAuraExclude, v.Name)

            if not Excluded and ((CurrentTeam == "Police" and PlayerTeam == "Criminal") or PlayerTeam == "Police") and PlayerTeam ~= CurrentTeam and v.Character and v.Character:FindFirstChild("HumanoidRootPart") and v.Character:FindFirstChild("Humanoid") and v.Character.Humanoid.Health > 0 then
                local Distance = DistanceXZ(v.Character.HumanoidRootPart.Position, HumanoidRootPart.Position)
                if Distance < NearestDistance then
                    NearestPlayer, NearestDistance = v, Distance
                end
            end
        end

        return NearestPlayer
    end

    function MoneyPerHour(MoneyEarned, TimeElapsed)
        return math.floor(3600 / TimeElapsed * MoneyEarned)
    end

    SetThread(2)

    GunShopUI.maid   = nil
    GunShopUI.open()

    local Connections = getconnections(LocalPlayer.PlayerGui.GunShopGui.Container.Container.Main.Container.Slider["Pistol"].Bottom.Action.MouseButton1Down)
    local Connection  = #Connections > 0 and Connections[1].Function

    if not Connection then
       setclipboard(string.format([[
           INFO : GUN_EQUIP_CONN_NIL
           EXECUTOR : %s
       ]], identifyexecutor()))
       Notification_new({
           Text = "Something went wrong while loading Jailbreaker. Info has been copied to your clipboard. Jailbreaker will proceed to run.",
           Duration = 10
       })
    end

    GunShopUI.close()
    SetThread(7)

    function GiveGun()
        if not Settings.KillAuraGun then
            Settings.KillAuraGun = "Pistol"
        end
            
        if not GunShopSystem.doesPlayerOwn(Settings.KillAuraGun) then
            Settings.KillAuraGun = "Pistol"
            spawn(function()
                Notification_new({
                    Text     = "You don't own this gun. KillAura gun has been set to Pistol 1",
                    Duration = 5
                })
            end)
        end

        if not Connection then
            for i,v in pairs(workspace.Givers:GetChildren()) do
                if v.Name == "Criminal" and v.Item.Value == "Pistol" then
                    fireclickdetector(v.ClickDetector)
                end
            end
            return
        end
        
        setupvalue(Connection, 1, {
            GetEquipped = function() 
                return false
            end
        })
        setupvalue(Connection, 3, Settings.KillAuraGun)
        setupvalue(Connection, 4, {
            doesPlayerOwn = function() 
                return true
            end
        })
        Connection()
    end

    function BuyGun(Gun)
        if not Connection then
            return
        end

        setupvalue(Connection, 1, {
            GetEquipped = function() 
                return false
            end
        })
        setupvalue(Connection, 3, Gun)
        setupvalue(Connection, 4, {
            doesPlayerOwn = function() 
                return false
            end
        })
        Connection()
    end

    function SetKillAuraGun(Name)
        Name = Name or "Pistol"
        
        local GunName = nil
        
        for i,v in pairs(Guns) do
            if v:lower():find(Name:lower()) then
                GunName = v
                break
            end
        end
        
        if not GunName then
            GunName = "Pistol"
            Notification_new({
                Text = "Invalid gun name. KillAura gun has been set to Pistol 2",
                Duration = 5
            })
        end
        
        if not GunShopSystem.doesPlayerOwn(GunName) then
            GunName = "Pistol"
            spawn(function()
                Notification_new({
                    Text     = "You don't own this gun. KillAura gun has been set to Pistol 3",
                    Duration = 5
                })
            end)
        end

        Settings.KillAuraGun = GunName
        
        GiveGun()
    end

    function Shoot()
        local CurrentEquipped = GetLocalEquipped()
        
        if not CurrentEquipped or not CurrentEquipped._attemptShoot then
            return
        end
        
        CurrentEquipped:InputBegan({
			UserInputType = Enum.UserInputType.MouseButton1
		})
    end

    function SilentAimSetTarget(Target)
        if Target then
            setupvalue(Update, 12, {
                RayIgnoreNonCollideWithIgnoreList = function(...)
                    if not Target then
                        setupvalue(Update, 12, {
                            RayIgnoreNonCollideWithIgnoreList = RayIgnoreNonCollideWithIgnoreList
                        })
                        return RayIgnoreNonCollideWithIgnoreList(...)
                    else
                        return Target, Target.Position, Target.Position
                    end
                end
            })
        else
            setupvalue(Update, 12, {
                RayIgnoreNonCollideWithIgnoreList = RayIgnoreNonCollideWithIgnoreList
            })
        end
    end

    function IsShipOutOfMap()
        local Ship = workspace:FindFirstChild("CargoShip")
        return not Ship or (Ship.PrimaryPart.Position.X < -3187 and Ship.PrimaryPart.Position.Z < 503)
    end

    function IsPlaneOutOfMap()
        local Plane = workspace:FindFirstChild("Plane")
        return not Plane or Plane.PrimaryPart.Position.Z < -5000
    end

    function IsCargoTrainOutOfMap(Gold)
        return Gold.Position.X < -1663 and Gold.Position.Z > 258
    end

    function SwitchTeam(Team)
        TeamId = ({
            ["Police"]   = 1,
            ["Prisoner"] = 2
        })[Team]

        if not TeamGui.Enabled then
            repeat
                TeamSwitchFunc()
                WaitUntil(function()
                    return TeamGui.Enabled
                end, 5)
            until TeamGui.Enabled
        end

        TeamJoinFunc = TeamJoinFunc or getconnections(TeamGui.Container.ContainerPlay.Play.MouseButton1Down)[1].Function

        setupvalue(TeamJoinFunc, 1, TeamId)

        repeat
            TeamJoinFunc()
            WaitUntil(function()
                return tostring(LocalPlayer.Team) == Team and not TeamGui.Enabled
            end, 5)
        until tostring(LocalPlayer.Team) == Team and not TeamGui.Enabled
    end

    function SetAutoExec(Loadstring)
        local Queue = (syn and syn.queue_on_teleport) or queue_on_teleport
        
        Queue(Loadstring)
    end

	function SwitchServer(SmallServer)
        AutoRobbing = false
        SwitchingServer = true

        if jbv2_key then
            SetAutoExec([[
                getgenv().V2_ServerHop = true
                getgenv().Last = ]]..tostring(Last)..[[
                getgenv().SecondElapsed = ]]..tostring(SecondElapsed)..[[
				getgenv().JB_NOGUI = ]]..tostring(JB_NOGUI)..[[
				getgenv().JB_DEBUG = ]]..tostring(JB_DEBUG)..[[
				getgenv().JB_DEVMODE = ]]..tostring(JB_DEVMODE)..[[
				getgenv().JB_NOAUTOEXEC = ]]..tostring(JB_NOAUTOEXEC)..[[
                jbv2_key = ']]..jbv2_key..[[';
            ]]..(JB_NOAUTOEXEC and "" or [[ loadstring(game:HttpGet("https://api.jailbreaker.site/getscript.php"))() ]]))
        else
            SetAutoExec([[
                getgenv().V2_ServerHop = true
                getgenv().Last = ]]..tostring(Last)..[[
                getgenv().SecondElapsed = ]]..tostring(SecondElapsed)..[[
				getgenv().JB_NOGUI = ]]..tostring(JB_NOGUI)..[[
				getgenv().JB_DEBUG = ]]..tostring(JB_DEBUG)..[[
				getgenv().JB_DEVMODE = ]]..tostring(JB_DEVMODE)..[[
				getgenv().JB_NOAUTOEXEC = ]]..tostring(JB_NOAUTOEXEC)..[[
            ]])
        end

        SetStatus("Switching Server")
            
        while true do
            Pcall(function()
                local AvailableServers = {}
                local Servers          = HttpService:JSONDecode(game:HttpGet("https://games.roblox.com/v1/games/606849621/servers/Public?limit=100"..(SmallServer and "&sortOrder=Asc" or "")))
                while #AvailableServers < 20 and Servers.nextPageCursor do
                    for _, v in pairs(Servers.data) do
                        if v.maxPlayers and v.playing then
                            if #AvailableServers >= 20 then
                                break
                            end
                            if v.maxPlayers - v.playing > 3 then
                                AvailableServers[#AvailableServers + 1] = v.id
                            end
                        end
                    end
                    Servers = HttpService:JSONDecode(game:HttpGet("https://games.roblox.com/v1/games/606849621/servers/Public?limit=100&cursor="..Servers.nextPageCursor..(SmallServer and "&sortOrder=Asc" or "")))
                    wait()
                end
                TeleportService:TeleportToPlaceInstance(606849621, AvailableServers[math.random(1, #AvailableServers)])
                wait(15)
            end, "SwitchServer")
            wait(2)
        end
    end

    function CheckAirdropAvailabilty()
        return (Robbery.CargoShip.Open and not IsShipOutOfMap()) or (Robbery.Mansion.Open and Inventory:FindFirstChild("MansionInvite")) or GetNearestAirdrop()
    end

    function GetPaths(Grid, Pairs)
        local Paths = {}

        for i = 0, #Pairs - 1 do
            local Pair  = Pairs[i]
            local Start = Pair[1]
            local End   = Pair[2]

            local Path    = {}
            local Current = Start

            table.insert(Path, Current)

            while not (Current.i == End.i and Current.j == End.j) do
                for x = -1, 1 do
                    for y = -1, 1 do
                        local Neighbor = Grid[Current.i + x] and Grid[Current.i + x][Current.j + y]
                        if Neighbor and Neighbor ~= Current and Neighbor.n == Current.n and not table.find(Path, Neighbor) then
                            table.insert(Path, Neighbor)
                            Current = Neighbor
                            break
                        end
                    end
                end
            end

            Paths[i] = Path
        end

        return Paths
    end

    function GetPairs(Grid)
        local Pairs = {}

        for i = 1, #Grid do
            for j = 1, #Grid[i] do
                local Cell = Grid[i][j]
                local NeighborCount = 0
                for k = -1, 1 do
                    for l = -1, 1 do
                        local Neighbor = Grid[i + k] and Grid[i + k][j + l]
                        if math.abs(k + l) == 1 and Neighbor and Neighbor == Cell then
                            NeighborCount = NeighborCount + 1
                        end
                    end
                end
                if NeighborCount == 1 then
                    if not Pairs[Cell] then
                        Pairs[Cell] = {}
                    end

                    table.insert(Pairs[Cell], {
                        Cell = Cell,
                        i = i,
                        j = j
                    })
                end
            end
        end

        return Pairs
    end

    function SolveNumberLink()
        if PlayerGui:FindFirstChild("FlowGui") then
            repeat task.wait()
                local Success = false

                Pcall(function()
                    local GridCopy = {}

                    for i = 1, #Puzzle.Grid do
                        GridCopy[i] = {}
                        for j = 1, #Puzzle.Grid[i] do
                            GridCopy[i][j] = Puzzle.Grid[i][j] + 1
                        end
                    end

                    local Body = Request({
                        Url = "https://numberlink-solver.brizzy9999.repl.co",
                        Method = "POST",
                        Body = Services.HttpService:JSONEncode({
                            Matrix = GridCopy
                        }),
                        Headers = {
                            ["Content-Type"] = "application/json"
                        }
                    }).Body

                    local Solution = HttpService:JSONDecode(Body).Solution

                    for i = 1, #Solution do
                        for j = 1, #Solution[i] do
                            Solution[i][j] = Solution[i][j] - 1
                        end
                    end

                    local Pairs = GetPairs(Solution)

                    for i = 0, #Pairs do
                        local Start = Pairs[i][1]
                        local End = Pairs[i][2]
                        local Current = Start

                        for _ = 1, 50 do
                            if not PlayerGui:FindFirstChild("FlowGui") then
                                break
                            end

                            for x = -1, 1 do
                                for y = -1, 1 do
                                    local Cell = Puzzle.Grid[Current.i + x] and Puzzle.Grid[Current.i + x][Current.j + y]
                                    local SolvedCell = Solution[Current.i + x] and Solution[Current.i + x][Current.j + y]

                                    if math.abs(x + y) == 1 and SolvedCell == Start.Cell and (Cell == -1 or (Current.i + x == End.i and Current.j + y == End.j)) then
                                        Puzzle.Grid[Current.i + x][Current.j + y] = SolvedCell
                                        Puzzle:Draw()
                                        Current = {
                                            i = Current.i + x,
                                            j = Current.j + y
                                        }
                                        break
                                    end
                                end
                            end

                            wait()

                            if Current and Current.i == End.i and Current.j == End.j then
                                Puzzle.OnConnection()
                                break
                            end
                        end
                    end

                    WaitUntil(function()
                        return not PlayerGui:FindFirstChild("FlowGui") or Check()
                    end, 5)

                    Success = true
                end, "SolveNumberlink")

                if not Success then
                    SetStatus("Solving Failed. Resetting Numberlink")
                    Puzzle:Reset()
                end
            until not PlayerGui:FindFirstChild("FlowGui") or Check()

            if Check() then
                return error()
            end
        end
    end

    function GetNearestBox()
        if Died then
            return
        end

        local BottomBoxes    = {}
        local SecondBoxes    = {}

        for i,v in pairs(Boxes:GetChildren()) do
            if v.Transparency < 0.9 then
                if v.Position.Y < 20 then
                    BottomBoxes[#BottomBoxes + 1] = v
                else
                    SecondBoxes[#SecondBoxes + 1] = v
                end
            end
        end

        table.sort(BottomBoxes, function(a, b)
            return DistanceXZ(a.Position, HumanoidRootPart.Position) < DistanceXZ(b.Position, HumanoidRootPart.Position)
        end)
        table.sort(SecondBoxes, function(a, b)
            return DistanceXZ(a.Position, HumanoidRootPart.Position) < DistanceXZ(b.Position, HumanoidRootPart.Position)
        end)

        if HumanoidRootPart.Position.Y < 35 then
            for i,v in pairs(BottomBoxes) do
                if not Raycast(Character.Head.Position, (v.Position + Vector3.new(0, 3, 0)) - Character.Head.Position) then
                    return v
                end
            end
        else
            for i,v in pairs(SecondBoxes) do
                if not Raycast(Character.Head.Position, (v.Position + Vector3.new(0, 3, 0)) - Character.Head.Position) then
                    return v
                end
            end
        end

        return HumanoidRootPart.Position.Y < 35 and BottomBoxes[1] or SecondBoxes[1]
    end

    function GetNearestGem()
        local Gems = {}

        for i,v in pairs(Tomb.Gems:GetChildren()) do
            if v.Outer.Transparency < 0.9 then
                Gems[#Gems + 1] = v
            end
        end

        table.sort(Gems, function(a, b)
            return DistanceXZ(a.Outer.Position, HumanoidRootPart.Position) < DistanceXZ(b.Outer.Position, HumanoidRootPart.Position)
        end)

        for i,v in pairs(Gems) do
            if not Raycast(v.Outer.Position + NewVector3(0, 3, 0), Character.Head.Position - (v.Outer.Position + NewVector3(0, 3, 0))) then
                return v
            end
        end

        return Gems[1]
    end

    function HackVault()
        local LED 		= Casino.HackableVaults.VaultDoorMain.InnerModel.Model.UnlockedLED
        local Attempts  = 0

        repeat
            for i, v in next, Specs do
                if v.Name == "Crack" then
                    v:Callback(true)
                end
            end

            if LED.BrickColor == BrickColor.new("Lime green") then
                for i, v in next, Specs do
                    if v.Name == "Change Direction" then
                        v:Callback(true)
                    end
                end

                WaitUntil(function()
                    return LED.BrickColor == BrickColor.new("Really red")
                end)
            end

            Attempts = Attempts + wait()
        until LED.CFrame.X < 179.7 or not Robbery.Casino.Open or Check() or Attempts > 30

        if not Robbery.Casino.Open or Check() or Attempts > 15 then
            return error()
        end
    end

    --// Buy Pisstol If Not Owned

    if not GunShopSystem.doesPlayerOwn("Pistol") then
        BuyGun("Pistol")
    end
end

--// Auto Rob Functions

do
    if JB_DEBUG then
        warn("[Jailbreaker Debugging]: Loading Auto Rob Functions..")
    end

	function RobCargoShip()
		-- if tostring(LocalPlayer.Team) ~= "Criminal" then
		-- 	SetStatus("Escaping")
		-- 	Escape()
		-- 	--Teleport(NewCFrame(-1020, 72, -1785), "Player", "Sky")
		-- 	Safety()

		-- 	if WaitUntil(function()
		-- 		return tostring(LocalPlayer.Team) == "Criminal"
		-- 	end, 10) then
		-- 		return error()
		-- 	end

		-- 	--wait(2)
		-- end
		
		local Crates = workspace.CargoShip.Crates
		
		for i = 1, 2 do
            --pcall(function()
                local Crate       = Crates:GetChildren()[i]
                local CurrentHeli = GetLocalVehicleModel()
                
                if not CurrentHeli or not table.find(Helis, CurrentHeli.Name) then
                    SetStatus("Getting Heli")
                    EnterVehicle("Heli")
                    
                    CurrentHeli = GetLocalVehicleModel()
                end

                if HumanoidRootPart.Position.Y + 10 < 400 then
                    
                    SetStatus("Teleporting Up")
                    
                    CurrentHeli.Engine.CFrame = NewCFrame(ToSky(CurrentHeli.Engine.Position, 400))
                    
                    wait(1)
                end
            
                if not CurrentHeli.Preset:FindFirstChild("RopePull") then
                    SetStatus("Dropping Rope")
                    repeat
                        Heli.attemptDropRope()
                        WaitUntil(function()
                            return GetLocalVehicleModel() and CurrentHeli.Preset:FindFirstChild("RopePull")
                        end, 5)
                    until not GetLocalVehicleModel() or (CurrentHeli.Preset:FindFirstChild("RopePull") and CurrentHeli.Preset.RopePull:FindFirstChild("ReqLink") and CurrentHeli.Preset.RopePull:FindFirstChild("AttachedTo")) or IsShipOutOfMap() or Crate.Parent ~= Crates
                end

                if IsShipOutOfMap() or Crate.Parent ~= Crates or not GetLocalVehicleModel() then
                    return
                end
                
                SetStatus("Attaching Crate")
                
                CurrentHeli.Winch.RopeConstraint.Length = 12000
                CurrentHeli.Preset.RopePull.CanCollide  = false

                repeat
                    if not CurrentHeli.Preset:FindFirstChild("RopePull") then
                        break
                    end

                    CurrentHeli.Preset.RopePull.CFrame  = Crate.PrimaryPart.CFrame
                    CurrentHeli.Preset.RopePull.ReqLink:FireServer(Crate, NewVector3(0, 0, 0))
                    wait()
                until not GetLocalVehicleModel() or not CurrentHeli.Preset:FindFirstChild("RopePull") or CurrentHeli.Preset.RopePull.AttachedTo.Value or Crate.Parent ~= Crates or IsShipOutOfMap()

                if IsShipOutOfMap() or not CurrentHeli.Preset:FindFirstChild("RopePull") or (Crate.Parent ~= Crates and not CurrentHeli.Preset.RopePull.AttachedTo.Value) or not GetLocalVehicleModel() then
                    return
                end

				if PlayerGui.AppUI:FindFirstChild("RewardSpinner") then
					SetStatus("Waiting For Reward Spinner To Finish Spinning")
					repeat wait() until not PlayerGui.AppUI:FindFirstChild("RewardSpinner")
				end
                
                SetStatus("Selling Crate")
                
                local Timeout = tick()
                        
                repeat
                    if Crate and Crate.PrimaryPart then
                        Crate.PrimaryPart.CFrame = NewCFrame(-475, -43, 1905)
                        wait()
                    end
                until not Crate or tick() - Timeout > 5 or not CurrentHeli.Preset:FindFirstChild("RopePull") or not CurrentHeli.Preset.RopePull.AttachedTo.Value
                
                repeat
					if not CurrentHeli.Preset:FindFirstChild("RopePull") then
						break
					end
                    CurrentHeli.Preset.RopePull.ReqUnlink:FireServer(Crate)
                    wait(0.1)
                until not CurrentHeli.Preset:FindFirstChild("RopePull") or not CurrentHeli.Preset.RopePull.AttachedTo.Value

                wait(0.5)
                
                Heli.attemptDropRope()

                wait(1)
            --end)
            if IsShipOutOfMap() then
                return error()
            end
		end

		SetStatus("Cargo Ship Success!")
		
		Robbery.CargoShip.Open = false
	end

	function RobMansion()
		GiveGun()
		
		SetStatus("Going to Mansion")

		if Robbery.Mansion.InstantTp then
			-- Teleport(NewCFrame(3195, 63, -4606), "Vehicle", "Instant", nil, function()
			-- 	if not Robbery.Mansion.Open then
			-- 		return "error"
			-- 	end
			-- end)

			AttemptJump()

			while true do
				if (ConfirmationGui.Enabled and ConfirmationMeesage.Text:find("Exit")) or (HumanoidRootPart.Position.Z < -4657) or not Robbery.Mansion.Open then
					break
				end

				HumanoidRootPart.CFrame = NewCFrame(3198, 63, -4656)
				wait()
			end
		else
			Platform.Position = NewVector3(2990, 55, -4607)
			Teleport(NewCFrame(2990, 58, -4607), "Vehicle", nil, nil, function()
				if not Robbery.Mansion.Open then
					return "error"
				end
			end)
			wait(0.1)
			AttemptJump()
			SetStatus("Going To Elevator")
			TeleportPath({
				NewCFrame(3083, 64, -4606),
				NewCFrame(3109, 68, -4606),
				NewCFrame(3197, 68, -4606)
			})
			
			repeat
				TeleportPath({
					NewCFrame(3197, 63, -4632),
					NewCFrame(3197, 63, -4654)
				})
	
				if WaitUntil(function()
					return (ConfirmationGui.Enabled and ConfirmationMeesage.Text:find("Exit")) or (HumanoidRootPart.Position.Z < -4657) or not Robbery.Mansion.Open
				end, 5) and Distance(HumanoidRootPart.Position, NewVector3(3198, 63, -4656)) < 2 or not Robbery.Mansion.Open then
					SetStatus("Full Players. Escaping")
	
					Robbery.Mansion.Open = false
	
					TeleportPath({
						NewCFrame(3195, 63, -4606),
						NewCFrame(3092, 62, -4605),
						NewCFrame(3063, 63, -4603),
						NewCFrame(3032, 57, -4544)
					})
			
					return
				end
			until (ConfirmationGui.Enabled and ConfirmationMeesage.Text:find("Exit")) or (HumanoidRootPart.Position.Z < -4657) or not Robbery.Mansion.Open
		end

		SetStatus("Waiting")

		if WaitUntil(function()
			return HumanoidRootPart.Position.Y < -190 or not Robbery.Mansion.Open
		end, 20) then
			SetStatus("Waiting Timed Out. Escaping")

			Robbery.Mansion.Open = false

			TeleportPath({
				NewCFrame(3197, 63, -4632),
				NewCFrame(3197, 68, -4606),
				NewCFrame(3109, 68, -4606),
				NewCFrame(3083, 64, -4606),
				NewCFrame(2990, 58, -4607)
			})

			return
		end

		if HumanoidRootPart.Position.Y > -190 and not Robbery.Mansion.Open then
			if not Robbery.Mansion.InstantTp then
				SetStatus("Waiting Timed Out. Escaping")

				Robbery.Mansion.Open = false

				TeleportPath({
					NewCFrame(3197, 63, -4632),
					NewCFrame(3197, 68, -4606),
					NewCFrame(3109, 68, -4606),
					NewCFrame(3083, 64, -4606),
					NewCFrame(2990, 58, -4607)
				})
			end

			return
		end

		local KillAuraStore = Settings.KillAura
		Settings.KillAura = false

		SetStatus("Going to CEO's office")

		if Robbery.Mansion.InstantTp then
			local Try = tick()

			repeat
				HumanoidRootPart.CFrame = NewCFrame(3154, -205, -4564)

				if tick() - Try > 3 then
					wait(1)
					Try = tick()
				else
					wait()
				end
			until Camera.CameraType ~= Enum.CameraType.Custom
		else
			wait(4.5)

			HumanoidRootPart.CFrame = NewCFrame(3202, -198, -4705)
			LaggedBack = false

			TeleportPath({
				NewCFrame(3204, -198, -4680),
				NewCFrame(3167, -198, -4681),
				NewCFrame(3106, -204, -4678),
				NewCFrame(3106, -204, -4651),
				NewCFrame(3126, -195, -4633),
				NewCFrame(3141, -206, -4610),
				NewCFrame(3152, -206, -4558),
				NewCFrame(3154, -204, -4545)
			})
		end

		SetStatus("Waiting")
		wait(30.5)

		SetStatus("Killing CEO")
		
		while MansionRobbery:FindFirstChild("ActiveBoss") and MansionRobbery.ActiveBoss.Humanoid.Health > 1 do
			if not Inventory:FindFirstChild(Settings.KillAuraGun) then
				GiveGun()
			else
				local CurrentEquipped = GetLocalEquipped()
				if not CurrentEquipped or CurrentEquipped.inventoryItemValue.Name ~= Settings.KillAuraGun then
					Inventory[Settings.KillAuraGun].InventoryEquipRemote:FireServer(true)
				else
					SilentAimSetTarget(MansionRobbery.ActiveBoss.Head)
					Shoot()
				end
			end
			wait()
		end

		Settings.KillAura = KillAuraStore

		if Distance(HumanoidRootPart.Position, NewVector3(3154, -204, -4564)) > 300 then
			return error()
		end
		
		WaitUntil(function()
			return not MansionRobbery:FindFirstChild("ActiveBoss")
		end)
		
		SilentAimSetTarget(nil)
		SetStatus("Escaping")

		if Robbery.Mansion.InstantTp then
			while true do
				if Distance(HumanoidRootPart.Position, Vector3.new(3105, 54, -4386)) < 50 then
					break
				end
				HumanoidRootPart.CFrame = NewCFrame(3064, -221, -4473)
				wait()
			end
		else
			TeleportPath({
				NewCFrame(3153, -201, -4506),
				NewCFrame(3131, -201, -4477),
				NewCFrame(3119, -204, -4439),
				NewCFrame(3098, -204, -4440),
				NewCFrame(3098, -205, -4451),
				NewCFrame(3097, -219, -4509),
				NewCFrame(3097, -219, -4518),
				NewCFrame(3076, -219, -4520),
				NewCFrame(3064, -221, -4473),
			})

			local WaitTime = tick()
			repeat wait() until Distance(HumanoidRootPart.Position, Vector3.new(3105, 54, -4386)) < 50 or (tick() - WaitTime) > 5
		end
		
        Teleport(NewCFrame(3082, 56, -4372))
		SetStatus("Mansion Success!")

		Robbery.Mansion.Open = false
	end

	function RobAirdrop(Retry)
		local Drop = GetNearestAirdrop()

		if not Drop or not Drop:FindFirstChild("Root") then
			return
		end

		if not Retry or DistanceXZ(HumanoidRootPart.Position, Drop.Root.Position) > 20 then
			SetStatus("Going to Airdrop")
            Platform.CFrame = NewCFrame(Drop.Root.Position)
			Teleport(Drop.Root.CFrame + NewVector3(-5, 3, 0), "Vehicle", nil, nil, function()
				if not Drop or not Drop:FindFirstChild("Root") then
					return "error"
				end
			end)
			wait(0.1)
			AttemptJump()
		end
		
		if not Drop or not Drop:FindFirstChild("Root") then
			return
		end

		if not Drop:GetAttribute("BriefcaseLanded") then
			SetStatus("Waiting for Airdrop to land")

			HumanoidRootPart.CFrame = NewCFrame(Raycast(HumanoidRootPart.Position, NewVector3(0, -1000, 0)).Position + NewVector3(0, 5, 0))

			WaitUntil(function()
				return Drop:GetAttribute("BriefcaseLanded")
			end, 30)

            Teleport(Drop.Root.CFrame + NewVector3(0, 6, 0))
		end

        SteppedSignals["Airdrop"] = RunService.Stepped:Connect(function()
            HumanoidRootPart.CFrame = Drop.Root.CFrame + NewVector3(0, 6, 0)
            HumanoidRootPart.Velocity = NewVector3(0, 0, 0)
        end)
		
		wait(0.5)
		
		LaggedBack = false

		SetStatus("Opening Airdrop")

		while Drop and Drop:FindFirstChild("Root") and not Drop:GetAttribute("BriefcaseCollected") and not Check() and not LaggedBack do
			Drop.BriefcasePress:FireServer(false)
			wait(0.1)
			Drop.BriefcaseRelease:FireServer(false)

			wait(0.5)
			
			local BriefcasePressed = Drop:GetAttribute("BriefcasePressAccumulation")

			print(25 - BriefcasePressed)

			Drop.BriefcasePress:FireServer(false)

            if WaitUntil(function()
				return not Drop or not Drop:FindFirstChild("Root") or Drop:GetAttribute("BriefcaseCollected") or Check() or LaggedBack
			end, 25 - BriefcasePressed) then
				Drop.BriefcasePress:FireServer(true)
				Drop.BriefcaseCollect:FireServer()
			end
		end

        SteppedSignals["Airdrop"]:Disconnect()

		if not Drop or not Drop:FindFirstChild("Root") or Check() or LaggedBack then
			return
		end

        HumanoidRootPart.CFrame = Drop.Root.CFrame + NewVector3(0, 6, 0)

        wait(1)
		SetStatus("Collecting Moneys")

		local Collected = false

		for i,v in pairs(DroppedCash:GetChildren()) do
			if v.PrimaryPart and v.PrimaryPart.Position.Y > 5 and Distance(v.PrimaryPart.Position, HumanoidRootPart.Position) < 30 then
				for i2,v2 in next, Specs do
					if v2.Part == v.PrimaryPart then
						v2:Callback(true)
						Collected = true
						break
					end
				end
			end
		end

		wait(1)

		for i,v in pairs(DroppedCash:GetChildren()) do
			if v.PrimaryPart and v.PrimaryPart.Position.Y > 5 and Distance(v.PrimaryPart.Position, HumanoidRootPart.Position) < 100 then
				Teleport(v.PrimaryPart.CFrame + NewVector3(0, 3, 0), "Player")
				wait(0.1)

				for i2,v2 in next, Specs do
					if v2.Part == v.PrimaryPart then
						v2:Callback(true)
						Collected = true
						break
					end
				end

				wait(0.1)
			end
		end

		SetStatus("Airdrop Success!")
	end

	function RobPowerPlant()
		SetStatus("Going To Power Plant")
		Teleport(NewCFrame(68, 21, 2339), "Vehicle", nil, nil, function()
			if not Robbery.PowerPlant.Open then
				return "error"
			end
		end)
		wait(0.1)
		AttemptJump()

		SetStatus("Going To Numberlink 1")
		Teleport(NewCFrame(87.40818786621094, 21.589290618896484, 2324.0126953125))

		if WaitUntil(function()
			return PlayerGui:FindFirstChild("FlowGui")
		end, 5) then
			Robbery.PowerPlant.Open = false
			return error()
		end

		--SetStatus("Waiting "..tostring(Settings.PowerPlantNumberlinkWait).."s..")
		--wait(Settings.PowerPlantNumberlinkWait)

		SetStatus("Solving Numberlink 1")
		SolveNumberLink()

		if not (PowerPlant.Door.Transparency > 0) then
			return error()
		end

		SetStatus("Going To Numberlink 2")

		TeleportPath({
			NewCFrame(94, 29, 2335),
			NewCFrame(146, 27, 2295),
			NewCFrame(209, 19, 2245),
			NewCFrame(146, -7, 2101),
			NewCFrame(120.3757095336914, -10.277959823608398, 2100.76318359375)
		}, function()
			if not Robbery.PowerPlant.Open then
				return "error"
			end
		end)

		if WaitUntil(function()
			return PlayerGui:FindFirstChild("FlowGui")
		end, 20) then
			Robbery.PowerPlant.Open = false
			return error()
		end

		--SetStatus("Waiting "..tostring(Settings.PowerPlantNumberlinkWait).."s..")
		--wait(Settings.PowerPlantNumberlinkWait)

		SetStatus("Solving Numberlink 2")
		SolveNumberLink()

		if not BagVisible() then
			Robbery.PowerPlant.Open = false
			return error()
		end

		SetStatus("Escaping")
		
		TeleportPath({
			NewCFrame(101, -6, 2108),
			NewCFrame(46, -10, 2100),
			NewCFrame(33, -13, 2126),
			NewCFrame(45, -14, 2164),
			NewCFrame(54, -7, 2182),
			NewCFrame(57, -2, 2206),
			NewCFrame(97, 16, 2257),
			NewCFrame(97, 23, 2257),
			NewCFrame(57, 21, 2309)
		})
		
		-- local Success = false

		-- spawn(function()
		-- 	repeat wait(0.1) until CheckUranium() <= ((Settings.PowerPlantUraniumValue or 5700) + 50)
		-- 	Success = true
		-- end)

		-- SetStatus("Going To Volcano Base")

		-- Platform.CFrame = NewCFrame(2293, 200, -2018)
		-- Teleport(NewCFrame(2293, 205, -2018), "Vehicle")
		
		-- SetStatus(("Waiting For Uranuim Value To Reach $%d"):format((Settings.PowerPlantUraniumValue or 5700) + 50))

		-- repeat wait(0.1) until Success

		AttemptSell("PowerPlant")
		SetStatus("Power Plant Success!")

		Robbery.PowerPlant.Open = false
	end

	function RobGasStation()
		SetStatus("Teleporting to Gas Station")

		Teleport(NewCFrame(-1603, 18, 662) * CFrame.Angles(0, math.rad(190), 0), "Vehicle", nil, nil, function()
			if not Robbery.Gas.Open then
				return
			end
		end)

		wait(0.2)

		SetStatus("Robbing Gas Station")

		for i,v in next, Specs do
			if v.Name == "Rob" and DistanceXZ(v.Part.Position, HumanoidRootPart.Position) < 70 then
				v:Callback(false)

				WaitUntil(function()
					return Check()
				end, 10)
				if Check() then
					return
				end

				v:Callback(true)
				break
			end
		end

		SetStatus("Gas Station Success!")
		
		Robbery.Gas.Open = false
	end

	function RobDonutStore()
		SetStatus("Teleporting to Donut Store")

		Teleport(NewCFrame(80, 33, -1596) * CFrame.Angles(0, math.rad(-16), 0), "Vehicle", nil, nil, function()
			if not Robbery.Donut.Open then
				return
			end
		end)

		wait(0.2)

		SetStatus("Robbing Donut Store")

		for i,v in next, Specs do
			if v.Name == "Rob" and DistanceXZ(v.Part.Position, HumanoidRootPart.Position) < 70 then
				v:Callback(false)
				
				WaitUntil(function()
					return Check()
				end, 10)
				if Check() then
					return
				end

				v:Callback(true)
				break
			end
		end

		SetStatus("Donut Store Success!")

		Robbery.Donut.Open = false
	end

	function RobCargoPlane()
		local Plane       = workspace.Plane
		local PlaneRoot   = Plane.PrimaryPart
		
		if Robbery.CargoPlane.InstantTp then
			if tostring(LocalPlayer.Team) ~= "Criminal" then
				SetStatus("Escaping")
				Escape()
				--Teleport(NewCFrame(-1020, 72, -1785), "Player", "Sky")
				Safety()

				if WaitUntil(function()
					return tostring(LocalPlayer.Team) == "Criminal"
				end, 10) then
					return error()
				end

				--wait(2)
			end

			SetStatus("Going To Cargo Plane")

			EnterVehicle()
		else
			SetStatus("Going To Cargo Plane")

			Teleport(function()
				return NewCFrame(PlaneRoot.Position + Vector3.new(0, 7, 0))
			end, "Vehicle", "Sky", nil, function()
				if IsPlaneOutOfMap() then
					return "error"
				end
			end)
		end
		
		SteppedSignals["PlaneTeleport"] = RunService.Stepped:Connect(function()
			if GetLocalVehicleModel() then
				GetLocalVehicleModel().PrimaryPart.CFrame = NewCFrame(PlaneRoot.Position + Vector3.new(0, 7, 0))
			else
				SteppedSignals["PlaneTeleport"]:Disconnect()
			end
		end)
		
		SetStatus("Grabbing Crate")

		repeat
			for i,v in next, Specs do
				if v.Name == "Inspect Crate" then
					v:Callback(true)
					break
				end
			end
			
			wait(0.01)
		until IsPlaneOutOfMap() or BagFull() or not GetLocalVehicleModel()

		SteppedSignals["PlaneTeleport"]:Disconnect()

		if not BagVisible() and (IsPlaneOutOfMap() or not GetLocalVehicleModel()) then
			return error()
		end

		AttemptSell("CargoPlane")

		SetStatus("Cargo Plane Success!")

		Robbery.CargoPlane.Open = false
	end

    function BottomToTop()
        local Paths = JewelryPaths[Jewelry.Floors:GetChildren()[1].Name]
		--// First floor
		if HumanoidRootPart.Position.Y < 25 then
            TeleportPath(Pathfind(HumanoidRootPart.Position, NewVector3(125, 23, 1337), 1, 5), nil, nil, true)
			TeleportPath({
				NewCFrame(107, 23, 1342),
				NewCFrame(97, 41, 1284),
				NewCFrame(107, 41, 1283)
			}, nil, nil, true)
		end
		--// Second floor
        TeleportPath(Pathfind(HumanoidRootPart.Position, NewVector3(125, 41, 1337), 1, 5), nil, nil, true)
		TeleportPath({
			NewCFrame(107, 41, 1342),
			NewCFrame(97, 62, 1284),
			NewCFrame(107, 62, 1283)
		}, nil, nil, true)
		--// Third floor
		TeleportPath(Paths[1], nil, nil, true)
		TeleportPath({
			NewCFrame(163, 66, 1332),
			NewCFrame(153, 83, 1274),
			NewCFrame(141, 83, 1277)
		}, nil, nil, true)
		--// Fourth floor
		TeleportPath(Paths[2], nil, nil, true)
		TeleportPath({
			NewCFrame(163, 90, 1332),
			NewCFrame(153, 107, 1274),
			NewCFrame(137, 107, 1277)
		}, nil, nil, true)
	end
	
	function TopToBottom(Pos)
        local Paths = JewelryPaths[Jewelry.Floors:GetChildren()[1].Name]
		--// Fourth floor
		TeleportPath({
			NewCFrame(153, 107, 1274),
			NewCFrame(163, 90, 1332),
			NewCFrame(137, 83, 1337)
		})
		TeleportPath(ReversePath(Paths[2]), nil, nil, true)
		--// Third floor
		TeleportPath({
			NewCFrame(153, 83, 1274),
			NewCFrame(163, 66, 1332),
			NewCFrame(137, 62, 1337)
		})
		TeleportPath(ReversePath(Paths[1]), nil, nil, true)
		--// Second floor
		TeleportPath({
			NewVector3(97, 62, 1284),
			NewVector3(107, 36, 1343),
			NewVector3(117, 36, 1341)
		})
	end

	function RobJewelry()
		SetStatus("Going To Jewelry")

		local LaserTouch = nil

		for i,v in pairs(Jewelry:GetChildren()) do
			if v.Name == "WindowEntry" and v.LaserWindow.Transparency ~= 1 then
				LaserTouch = v.LaserTouch
			end
		end

		if not LaserTouch then
			local LaserTouches = {}

			for i,v in pairs(Jewelry:GetChildren()) do
				if v.Name == "WindowEntry" then    
					table.insert(LaserTouches, v.LaserTouch)
				end
			end

			table.sort(LaserTouches, function(a, b)
				return DistanceXZ(HumanoidRootPart.Position, a.Position) < DistanceXZ(HumanoidRootPart.Position, b.Position)
			end)

			LaserTouch = LaserTouches[1]

			local OldPosition = LaserTouch.Position
			LaserTouch.Position = HumanoidRootPart.Position
			wait()
			LaserTouch.Position = OldPosition
		end

		if Robbery.Jewelry.InstantTp then
			Teleport(NewCFrame(120, 36, 1309) * CFrame.Angles(0, math.rad(98), 0), "Vehicle", "Instant", nil, function()
				if not Robbery.Jewelry.Open then
					return "error"
				end
			end)
		elseif RobberyState[tostring(Robbery.Jewelry.id)].Value == 2 then
			Teleport(NewCFrame(155, 118, 1337), "Vehicle", nil, nil, function()
				if not Robbery.Jewelry.Open then
					return "error"
				end
			end)
			
			wait(0.1)
			AttemptJump()
			wait(0.1)

			SetStatus("Going To Bottom Floor")

			TeleportPath({
				NewCFrame(139, 118, 1315),
				NewCFrame(138, 118, 1307),
				NewCFrame(122, 118, 1282),
				NewCFrame(113, 118, 1282),
				NewCFrame(115, 118, 1292),
				NewCFrame(123, 105, 1340),
				NewCFrame(137, 105, 1338),
				NewCFrame(136, 105, 1277)
			})

			TopToBottom()
		else
			if Distance(LaserTouch.Position, NewVector3(91, 18, 1311)) < 20 then
				Teleport(NewCFrame(63, 18, 1316), "Vehicle", nil, nil, function()
					if not Robbery.Jewelry.Open then
						return "error"
					end
				end)

				wait(0.1)
				AttemptJump()

				SetStatus("Breaking In")

				Teleport(NewCFrame(78, 18, 1313))
				Teleport(NewCFrame(91, 18, 1311))
				Teleport(NewCFrame(100, 18, 1309))
				Teleport(NewCFrame(98, 17, 1291))
			else
				Teleport(NewCFrame(136, 18, 1374), "Vehicle", nil, nil, function()
					if not Robbery.Jewelry.Open then
						return "error"
					end
				end)

				wait(0.1)
				AttemptJump()

				SetStatus("Breaking In")

				Teleport(NewCFrame(136, 18, 1346))
				Teleport(NewCFrame(125, 18, 1328))
				Teleport(NewCFrame(98, 17, 1291))
			end
		end

		local KillAuraStore = Settings.KillAura
		Settings.KillAura = false

		local PathfindFailed = 0

		while not BagFull() and Robbery.Jewelry.Open and not Check() do
			local NearestBox = GetNearestBox()

			if not NearestBox then
				break
			end

			SetStatus("Going To Box")

			local NextToBox = (NearestBox.CFrame   * NewCFrame(0, -3, 0)).p
			local AboveBox  = (NearestBox.CFrame   + NewVector3(0, 5, 0)).p

			if Distance(HumanoidRootPart.Position, NewVector3(98, 17, 1291)) > 200 then
				return error()
			end

			if not Raycast(Character.Head.Position, AboveBox - Character.Head.Position) then
				if not Raycast(HumanoidRootPart.Position, NextToBox - HumanoidRootPart.Position) and DistanceXZ(HumanoidRootPart.Position, NextToBox) < 20 then
					HumanoidRootPart.CFrame = NewCFrame(NextToBox, NearestBox.Position)
				else
					HumanoidRootPart.CFrame = HumanoidRootPart.CFrame + Vector3.new(0, 4, 0)
					Teleport(NewCFrame(NextToBox, NearestBox.Position), "Player", "Direct", nil, nil, NewVector3(0, 4, 0))
				end
			else
				local PathToBox = Pathfind(HumanoidRootPart.Position, NextToBox, 1, 5)
				if PathToBox then
					TeleportPath(PathToBox, nil, nil, true)
					HumanoidRootPart.CFrame = NewCFrame(NextToBox, NearestBox.Position)
				end
			end

			if PathfindFailed >= 3 then
				SetStatus("Max Pathfind Attempt.")
				return error()
			end

			if Distance(HumanoidRootPart.Position, NearestBox.Position) > 7 then
				PathfindFailed = PathfindFailed + 1
			else
				SetStatus("Punching Boxes")

                getfenv(Punch).tick = function() return 1/0 end

				for i = 1, 4, 0.1 do
					if GetLocalEquipped() and GetLocalEquipped().inventoryItemValue:FindFirstChild("InventoryEquipRemote") then
						GetLocalEquipped().inventoryItemValue.InventoryEquipRemote:FireServer(false)
					end
					
					if Distance(HumanoidRootPart.Position, NextToBox) > 3 then
						break
					end

					Punch()

					wait(0.1)

					if Check() then
						return
					elseif LaggedBack or NearestBox.Transparency > 0.9 then
						break
					end
				end

                getfenv(Punch).tick = tick
			end

			wait()
		end

		Settings.KillAura = KillAuraStore

		if not BagVisible() then
			return
		end
		
		wait(1.5)

		SetStatus("Escaping")

		BottomToTop()
        TeleportPath({
            NewCFrame(137, 105, 1338),
            NewCFrame(123, 105, 1340),
            NewCFrame(115, 118, 1292),
            NewCFrame(112, 118, 1281),
			NewCFrame(97, 118, 1284)
        })

		wait(0.5)
				
        -- wait(0.5)
        -- HumanoidRootPart.CFrame = NewCFrame(97, 118, 1284)
		-- LaggedBack = false
        -- wait(0.5)
        
		Robbery.Jewelry.Open = false

		AttemptSell("Jewelry")
		SetStatus("Jewelry Success!")
	end

	function RobCargoTrain()
		local BoxCar = GetCargoTrainBoxCar()

		if not BoxCar then
			SetStatus("Waiting For Cargo Train To Enter The Map")

			WaitUntil(function()
				BoxCar = GetCargoTrainBoxCar()
				return BoxCar
			end, nil, 1)
		end

		local Gold = BoxCar.Model.Rob.Gold

		SetStatus("Going To Cargo Train")
		
		if false then
			for i,v in next, Specs do
				if v.Name == "Open Door" and v.Part:IsDescendantOf(BoxCar) then
					v:Callback(true)
					break
				end
			end
			for i,v in next, Specs do
				if v.Name == "Breach Vault" and v.Part:IsDescendantOf(BoxCar) then
					v:Callback(true)
					break
				end
			end

			wait(0.5)
		else
			Teleport(function()
				return NewCFrame(ToSky(Gold.Position, 400))
			end, "Vehicle", "Sky", nil, function()
				if IsCargoTrainOutOfMap(Gold) then
					return "error"
				end
			end)

			if Raycast(Gold.Position, NewVector3(0, 100, 0)) then
				SetStatus("Waiting For Cargo Train To Leave The Tunnel")

				local CurrentVehicle = GetLocalVehicleModel()
				local BV             = Instance.new("BodyVelocity", CurrentVehicle.PrimaryPart)

				BV.Velocity          = NewVector3(0, 0, 0)
				BV.MaxForce          = NewVector3(9e9, 9e9, 9e9)

				SteppedSignals["WaitForCargoTrain"] = RunService.Stepped:Connect(function()
					if GetLocalVehicleModel() then
						GetLocalVehicleModel().PrimaryPart.CFrame = NewCFrame(ToSky(Gold.Position, 400))
					else
						SteppedSignals["WaitForCargoTrain"]:Disconnect()
					end
				end)

				WaitUntil(function()
					return not Raycast(Gold.Position, NewVector3(0, 100, 0)) or not GetLocalVehicleModel() or IsCargoTrainOutOfMap(Gold)
				end, nil, 0.5)

				if not GetLocalVehicleModel() or IsCargoTrainOutOfMap(Gold) then
					SteppedSignals["WaitForCargoTrain"]:Disconnect()
					return error()
				end
				
				wait(1)

				SteppedSignals["WaitForCargoTrain"]:Disconnect()

				BV:Destroy()
			end
		end

        GetLocalVehicleModel().PrimaryPart.CFrame = Gold.CFrame + Vector3.new(0, 15, 0)
		SetStatus("Breaching Vault")

		wait(1)

		for i,v in next, Specs do
			if v.Name == "Open Door" and v.Part:IsDescendantOf(BoxCar) then
				v:Callback(true)
				break
			end
		end
		for i,v in next, Specs do
			if v.Name == "Breach Vault" and v.Part:IsDescendantOf(BoxCar) then
				v:Callback(true)
				break
			end
		end

		AttemptJump()

        Humanoid.Sit = false
		EnteringCar = true

		SetStatus("Collecting Gold")
        SteppedSignals["GoldTP"] = RunService.Stepped:Connect(function()
            HumanoidRootPart.CFrame = Gold.CFrame + Vector3.new(0, 5, 0)
        end)

		if WaitUntil(function()
			return BagVisible()
		end, 5) then
			return error()
		end

		LaggedBack = false

		if WaitUntil(function()
			return BagFull() or Check() or IsCargoTrainOutOfMap(Gold) or LaggedBack
		end, 50) then
			if not Check() then
				Robbery.CargoTrain.Open = false
			end
			return error()
		end

		LaggedBack = false

		if Check() or IsCargoTrainOutOfMap(Gold) or LaggedBack then
			SteppedSignals["GoldTP"]:Disconnect()
			return error()
		end

		if Raycast(Gold.Position, NewVector3(0, 100, 0)) then
			SetStatus("Waiting For Cargo Train To Leave The Tunnel")

			WaitUntil(function()
				return not Raycast(Gold.Position, NewVector3(0, 100, 0))
			end)
			
			wait(1)
		end

		EnteringCar = false

		SteppedSignals["GoldTP"]:Disconnect()
		wait()
		Safety()

		WaitUntil(function()
			return not BagVisible()
		end, 5)

		SetStatus("Cargo Train Success!")

		Robbery.CargoTrain.Open = false
	end

	function RobPassengerTrain()
		if tostring(LocalPlayer.Team) ~= "Criminal" then
			SetStatus("Escaping")
			Escape()
			--Teleport(NewCFrame(-1020, 72, -1785), "Player", "Sky")
			Safety()

			if WaitUntil(function()
				return tostring(LocalPlayer.Team) == "Criminal"
			end, 10) then
				return error()
			end

			--wait(2)
		end

		local Success   = false
		local StartTick = tick()

		spawn(function()
			SetStatus("Filling Bag")

			for i,v in next, Specs do
				if v.Name:match("Grab") and v.Part:IsDescendantOf(workspace.Trains) then
					if BagFull() then
						break
					end

					v:Callback(true)
					wait(1)
				end
			end

			Success = true
		end)

		Platform.CFrame = NewCFrame(2293, 200, -2018)
		Teleport(NewCFrame(2293, 205, -2018), "Vehicle")
		repeat wait() until Success or (tick() - StartTick) > 30

		if not BagVisible() then
			error()
		end

		AttemptSell("Passenger")
		SetStatus("Passenger Train Success!")

		Robbery.PassengerTrain.Open = false
	end

	function RobBank()
		SetStatus("Going To Bank")

		local PathToVault
		local InVault = false

		if Robbery.Bank.InstantTp then
			Teleport(NewCFrame(39, 18, 925), "Vehicle", "Instant", nil, function()
				if not Robbery.Bank.Open then
					return "error"
				end
			end)
		else
			Teleport(NewCFrame(-8, 18, 865), "Vehicle", nil, nil, function()
				if not Robbery.Bank.Open then
					return "error"
				end
			end)

			wait(0.1)
			AttemptJump()

			SetStatus("Entering Bank")

			Teleport(NewCFrame(3, 18, 863))
			Teleport(NewCFrame(28, 18, 859))
			Teleport(NewCFrame(39, 18, 925))
		end

		-- if not Bank or not Ringers:FindFirstChild("Bank") then
		-- 	SetStatus("Waiting For Bank To Load")
		-- 	repeat wait() until Bank and Ringers:FindFirstChild("Bank")
		-- end

		if not InVault then
			SetStatus("Waiting")

			if WaitUntil(function()
				return not Ringers:FindFirstChild("Bank") or #Ringers.Bank:GetChildren() > 0 or not Robbery.Bank.Open
			end, 5) then
				return error()
			end

			local Layout = Bank.Layout:GetChildren()[1]
			local OldPosition = Layout.TriggerDoor.Position

			Layout.TriggerDoor.Position = HumanoidRootPart.Position
			Wait()
			Layout.TriggerDoor.Position = OldPosition

			if Layout:FindFirstChild("Door") then
				for i,v in pairs(Layout.Door:GetDescendants()) do
					if v:IsA("BasePart") then
						v.CanCollide = false
					end
				end
			end

			PathToVault = BankPaths[Layout.Name]
			
			if PathToVault then
				-- PathToVault = IncreasePathHeight(PathToVault)

				local Path = {}

				for i,v in pairs(PathToVault) do
					table.insert(Path, NewCFrame(v + NewVector3(0, 3, 0)))
				end

				PathToVault = Path

				SetStatus("Going To Bank Vault")

				TeleportPath(PathToVault, function()
					if not Robbery.Bank.Open or Check() then
						return "error"
					end

					return CopEntered()
				end, nil, true)

				HumanoidRootPart.CFrame = NewCFrame(PathToVault[#PathToVault])
			end
		end

		if PathToVault then
			if not CopEntered() then
				SetStatus("Collecting Money")

				if WaitUntil(function()
					return BagVisible() or not Robbery.Bank.Open or Check() or CopEntered() or Humanoid.Health <= 10 or (BagVisible() and (tonumber(PlayerGui.RobberyMoneyGui.Container.Bottom.Time.Text:match("%d+")) or 60) < 15 and PlayerGui.RobberyMoneyGui.Container.Bottom.Time.Visible)
				end, 30) then
					return error()
				end

				if WaitUntil(function()
					return BagFull() or not Robbery.Bank.Open or Check() or CopEntered() or Humanoid.Health <= 10 or (BagVisible() and (tonumber(PlayerGui.RobberyMoneyGui.Container.Bottom.Time.Text:match("%d+")) or 60) < 15 and PlayerGui.RobberyMoneyGui.Container.Bottom.Time.Visible)
				end, 100) then
					return error()
				end
				
				if not Robbery.Bank.Open or Check() then
					return error()
				end
			end

			if CopEntered() then
				SetStatus("Cop Entered. Escaping")
			elseif Humanoid.Health <= 10 then
				SetStatus("Low Health. Escaping")
			elseif BagVisible() and (tonumber(PlayerGui.RobberyMoneyGui.Container.Bottom.Time.Text:match("%d+")) or 60) < 15 and PlayerGui.RobberyMoneyGui.Container.Bottom.Time.Visible then
				SetStatus("Bank Closing. Escaping")
			else
				SetStatus("Escaping")
			end

			local EscapePath = {}
			
			for i = #PathToVault, 1, -1 do
				table.insert(EscapePath, PathToVault[i])
			end

			TeleportPath(EscapePath, function()
				if not Robbery.Bank.Open or Check() then
					return "error"
				end
			end, true, true)
		else
			SetStatus("Unsupported Bank Layout. Escaping")
		end

		Teleport(NewCFrame(39, 18, 925))
		Teleport(NewCFrame(28, 18, 859))
		Teleport(NewCFrame(-8, 18, 865))

		Safety()

		WaitUntil(function()
			return not BagVisible()
		end, 5)

		SetStatus("Bank Success!")

		Robbery.Bank.Open = false
	end

	--// Currently Testing

	function RobMuseum()
		if Robbery.Museum.InstantTp and tostring(LocalPlayer.Team) ~= "Criminal" then
			SetStatus("Escaping")
			Escape()
			--Teleport(NewCFrame(-1020, 72, -1785), "Player", "Sky")
			Safety()

			if WaitUntil(function()
				return tostring(LocalPlayer.Team) == "Criminal"
			end, 10) then
				return error()
			end

			--wait(2)
		end
		
		SetStatus("Going To Museum")

		if Museum and Museum.LargeJewel.Jewel.Transparency < 1 then
			if Robbery.Museum.InstantTp then
				Teleport(NewCFrame(1061, 102, 1361) * CFrame.Angles(0, math.rad(325), 0), "Vehicle", "Instant", nil, function()
					if not Robbery.Museum.Open then
						return "error"
					end
				end)
			else
				Teleport(NewCFrame(1046, 101, 1381), "Vehicle", nil, nil, function()
					if not Robbery.Museum.Open then
						return "error"
					end
				end)
				
				wait(0.1)
				AttemptJump()
				wait(0.1)
				
				TeleportPath({NewCFrame(1054, 102, 1370)}, nil, nil, true)
			end

			TeleportPath({NewCFrame(1068, 102, 1353)}, nil, nil, true)

			wait(0.2)

			for i,v in next, Specs do
				if v.Name == "Grab Jewel" and Distance(HumanoidRootPart.Position, v.Part.Position) < 20 then
					v:Callback(true)
					break
				end
			end

			WaitUntil(function()
				return BagVisible()
			end, 5)

			TeleportPath({
				NewCFrame(1054, 102, 1370),
				NewCFrame(1046, 101, 1381)
			})
		elseif Museum and Museum.MummyCase.Statues[""].Head.Transparency < 1 then
			if Robbery.Museum.InstantTp then
				Teleport(NewCFrame(1167, 102, 1226) * CFrame.Angles(0, math.rad(142), 0), "Vehicle", "Instant", nil, function()
					if not Robbery.Museum.Open then
						return
					end
				end)
			else
				Teleport(NewCFrame(1187, 101, 1200), "Vehicle", nil, nil, function()
					if not Robbery.Museum.Open then
						return
					end
				end)
				
				wait(0.1)
				AttemptJump()
				wait(0.1)
				
				TeleportPath({NewCFrame(1177, 102, 1213)}, nil, nil, true)
			end

			TeleportPath({NewCFrame(1158, 102, 1237)}, nil, nil, true)

			wait(0.2)

			for i,v in next, Specs do
				if v.Name == "Grab Mummy" and Distance(HumanoidRootPart.Position, v.Part.Position) < 20 then
					v:Callback(true)
					break
				end
			end

			WaitUntil(function()
				return BagVisible()
			end, 5)

			TeleportPath({
				NewCFrame(1177, 102, 1213),
				NewCFrame(1187, 101, 1200)
			})
		end

		if not Robbery.Museum.Open or Check() then
			return error()
		end

		if not BagFull() then
			if Robbery.Museum.InstantTp then
				Teleport(NewCFrame(1112, 106, 1291), "Vehicle", "Instant", nil, function()
					if not Robbery.Museum.Open then
						return
					end
				end)
			else
				Teleport(NewCFrame(1124, 139, 1299), "Vehicle", nil, nil, function()
					if not Robbery.Museum.Open then
						return
					end
				end)

				wait(0.1)
				AttemptJump()
				wait(0.1)

				SetStatus("Going in")
				TeleportPath({
					NewCFrame(1081, 139, 1313),
					NewCFrame(1081, 122, 1313),
					NewCFrame(1096, 106, 1288),
					NewCFrame(1101, 106, 1282),
					NewCFrame(1112, 106, 1291)
				}, function()
					if not Robbery.Museum.Open then
						return
					end
				end)
			end

			SetStatus("Filling Bag")

			for i,v in pairs(MuseumObjects) do
				if not Robbery.Museum.Open or Check() then
					return error()
				end

				if BagFull() then
					break
				end

				local Object   = v[1]
				local CF       = v[2]

				if Object.Transparency < 0.6 then
					if Raycast(HumanoidRootPart.Position, CF.p - HumanoidRootPart.Position) then
						Teleport(NewCFrame(1124, 107, 1300))
					end

					Teleport(CF)

					wait(0.2)

					for i2,v2 in next, Specs do
						if v2.Part == Object then
							v2:Callback(true)
							break
						end
					end
				end
			end

			if not BagFull() then
				if not Robbery.Museum.Open or Check() then
					return error()
				end

				Teleport(NewCFrame(1124, 107, 1300))

				for i,v in next, Specs do
					if v.Name == "Grab Bone" then
						if BagFull() then
							break
						end

						v:Callback(true)

						wait(1)
					end
				end
			end

			TeleportPath({
				NewCFrame(1101, 106, 1282),
				NewCFrame(1096, 106, 1288),
				NewCFrame(1081, 122, 1313),
				NewCFrame(1081, 139, 1313),
				NewCFrame(1124, 139, 1299)
			}, function()
				if not Robbery.Museum.Open then
					return
				end
			end)
		end

		if not BagVisible() then
			return
		end
		
		if CheckPowerPlant() and Robbery.PowerPlant.Enabled then
			RobPowerPlant()
		else
			SetStatus("Going To Volcano Base")

			Teleport(function()
				Platform.CFrame = NewCFrame(2293, 200, -2018)
				return NewCFrame(2293, 205, -2018)
			end, "Vehicle")

			SetStatus("Waiting "..(Settings.MuseumSellWait).."s")
			wait(Settings.MuseumSellWait)

			AttemptSell("Museum")
		end

        Robbery.Museum.Open = false
		SetStatus("Museum Success!")
	end

	function RobCasino()
		SetStatus("Going To Casino")

		local HackedPCs   = false
		local AtVault     = false
		local HackedVault = false
		
		for i,v in pairs(Casino and Casino.Computers:GetChildren() or {}) do
			if v:GetAttribute("ShowDisableSecurityPrompt") and not v:GetAttribute("ComputerActive") then
				HackedPCs = true
			end
		end

		if Robbery.Casino.InstantTp then
			if HackedPCs then
				local LED = Casino and Casino.HackableVaults.VaultDoorMain.InnerModel.Model.UnlockedLED
				if LED.CFrame.X < 179.7 then
					Teleport(NewCFrame(206, -77, -4528), "Vehicle", "Instant", nil, function()
						if not Robbery.Casino.Open then
							return "error"
						end
					end)
					
					AtVault     = true
					HackedVault = true
				else
					Teleport(NewCFrame(174, -77, -4527), "Vehicle", "Instant", nil, function()
						if not Robbery.Casino.Open then
							return "error"
						end
					end)
					AtVault = true
				end
			else
				Teleport(NewCFrame(-114, 73, -4620), "Vehicle", "Instant", nil, function()
					if not Robbery.Casino.Open then
						return "error"
					end
				end)
				Teleport(NewCFrame(-114, 73, -4620))
			end
		else
			Teleport(NewCFrame(46, 155, -4740), "Vehicle", nil, nil, function()
				if not Robbery.Casino.Open then
					return "error"
				end
			end)

			wait(0.1)
			AttemptJump()
			wait(0.1)

			if not HackedPCs then
				SetStatus("Going To Security Floor")
			else
				SetStatus("Going To Vault Floor")
			end

			Platform.CFrame = NewCFrame(-17, 153, -4753)

			TeleportPath({
				NewCFrame(-13, 155, -4738),
				NewCFrame(-17, 155, -4753)
			})

			wait(0.2)
		end

		if not HackedPCs then
			if not Robbery.Casino.InstantTp then
				Platform.CFrame         = NewCFrame(-17, 70, -4753)
				HumanoidRootPart.CFrame = NewCFrame(-17, 73, -4753)

				wait(0.2)

				TeleportPath({
					NewCFrame(-14, 73, -4740),
					NewCFrame(-114, 73, -4620)
				})
			end

			SetStatus("Hacking PCs")

			local Success = false

			while not Success do
				local Computers = {}

				for i,v in pairs(Casino.Computers:GetChildren()) do
					if v:GetAttribute("ShowDisableSecurityPrompt") and not v:GetAttribute("ComputerActive") then
						Success = true
					elseif v:GetAttribute("ComputerActive") then
						table.insert(Computers, v)
					end
				end

				if Success then
					continue
				end

				table.sort(Computers, function(a, b)
					return Distance(HumanoidRootPart.Position, a.Display.Position) < Distance(HumanoidRootPart.Position, b.Display.Position)
				end)

				repeat
					TeleportPath({NewCFrame(Computers[1].Display.Position + NewVector3(0, 5, 0))})
					
					for i,v in next, Specs do
						if v.Part == Computers[1].Display then
							v:Callback(true)
							break
						end
					end

					wait()
				until not Computers[1]:GetAttribute("ComputerActive") or Computers[1]:GetAttribute("ShowDisableSecurityPrompt")

				if Computers[1]:GetAttribute("ShowDisableSecurityPrompt") then
					for i,v in next, Specs do
						if v.Part == Computers[1].Display then
						v:Callback(true)
							break
						end
					end

					Success = true
				end

				wait()
			end
			
			local LeavePositions = {
				{
					NewVector3(-38, 73, -4663),
					NewVector3(-45, 73, -4688)
				},
				{
					NewVector3(46, 73, -4686),
					NewVector3(38, 71, -4712)
				}
			}

			table.sort(LeavePositions, function(a, b)
				return Distance(HumanoidRootPart.Position, a[1]) < Distance(HumanoidRootPart.Position, b[1])
			end)

			if Raycast(HumanoidRootPart.Position, LeavePositions[1][2] - HumanoidRootPart.Position) then
				Teleport(NewCFrame(LeavePositions[1][1]), "Player", "Direct", nil, function()
					if not Robbery.Casino.Open then
						return "error"
					end
				end)
			end
			if Raycast(HumanoidRootPart.Position, NewVector3(-14, 73, -4740) - HumanoidRootPart.Position) then
				Teleport(NewCFrame(LeavePositions[1][2]), "Player", "Direct", nil, function()
					if not Robbery.Casino.Open then
						return "error"
					end
				end) 
			end

			Platform.CFrame         = NewCFrame(-17, 72, -4753)

			TeleportPath({
				NewCFrame(-14, 75, -4740),
				NewCFrame(-17, 75, -4753)
			})

			wait(0.2)
		end

		if not AtVault then
			SetStatus("Going To Vault Floor")

			Platform.CFrame         = NewCFrame(-17, -76, -4753)
			HumanoidRootPart.CFrame = NewCFrame(-17, -73, -4753)

			wait(0.2)

			TeleportPath({
				NewCFrame(-14, -73, -4740),
				NewCFrame(-41.930301666259766, -76.9753646850586, -4732.89794921875)
			})

			HumanoidRootPart.CFrame = NewCFrame(-41.930301666259766, -76.9753646850586, -4732.89794921875)

			wait(0.3)

			SetStatus("Breaking Glass")

			for i,v in pairs(Casino:GetChildren()) do
				if v.Name == "Glass" and Distance(v.Position, HumanoidRootPart.Position) < 9 then
					v.CutRemote:FireServer()
					if v.Transparency ~= 1 then
						if WaitUntil(function()
							return v.Transparency == 1
						end, 10) then
							return error()
						end

						wait(0.4)

						WaitUntil(function()
							local RaycastResult = Raycast(NewVector3(-41.930301666259766, -76.9753646850586, -4732.89794921875), NewVector3(-45.318729400634766, -77.27167510986328, -4731.205078125) - NewVector3(-41.930301666259766, -76.9753646850586, -4732.89794921875))
							return not RaycastResult or not RaycastResult.Instance.CanCollide
						end, 5)
					end

					HumanoidRootPart.CFrame = NewCFrame(-45.318729400634766, -77.27167510986328, -4731.205078125)

					wait(0.2)

                    LaggedBack = false
				end
			end

			SetStatus("Going To Main Vault")

			TeleportPath({
				NewCFrame(-44, -78, -4701),
				NewCFrame(-31, -77, -4645),
				NewCFrame(7, -77, -4656),
				NewCFrame(33, -77, -4585),
				NewCFrame(59, -77, -4554),
				NewCFrame(94, -77, -4534),
				NewCFrame(174, -77, -4527)
			})
		end

		if not HackedVault then
			SetStatus("Hacking Main Vault")

			HackVault()

			Teleport(NewCFrame(206, -75, -4528))
		end

		--Teleport(NewCFrame(189, -68, -4526))
		--Teleport(NewCFrame(213, -68, -4555))
		Teleport(NewCFrame(241, -75, -4532))

		SetStatus("Collecting Loots")

		local Success = false
		local StartTick = tick()

		spawn(function()
			while not Success and not BagFull() and Robbery.Casino.Open and not Check() do
				for i,v in pairs(Casino.Loots:GetChildren()) do
					if v.Name == "Casino_Cash" and Distance(HumanoidRootPart.Position, v.Position) < 30 then
						v.CasinoLootCollect:FireServer()
					end
				end

				wait(0.1)
			end
		end)

		while not BagFull() and Robbery.Casino.Open and not Check() do
			local Cashes = {}

			for i,v in pairs(Casino.Loots:GetChildren()) do
				if v.Name == "Casino_Cash" and not Raycast(HumanoidRootPart.Position, (v.Position + NewVector3(0, 5, 0)) - HumanoidRootPart.Position) then
					table.insert(Cashes, v)
				end
			end

			table.sort(Cashes, function(a, b)
				return Distance(a.Position, HumanoidRootPart.Position) < Distance(b.Position, HumanoidRootPart.Position)
			end)

			if not Cashes[1] then
				SetStatus("No Loot Available. Escaping")

				wait(1)

				break
			end

			repeat
				if DistanceXZ(HumanoidRootPart.Position, Cashes[1].Position) < 20 then
					HumanoidRootPart.CFrame = NewCFrame(Cashes[1].Position + NewVector3(0, 5, 0))
				else
					Teleport(NewCFrame(Cashes[1].Position + NewVector3(0, 5, 0)))
				end

				wait()
			until Cashes[1].Parent ~= Casino.Loots or BagFull() or not Robbery.Casino.Open or Check()

			wait()
		end

		Success = true

		if not Robbery.Casino.Open or Check() then
			return error()
		end

		SetStatus("Escaping")

		TeleportPath({
			NewCFrame(241, -68, -4532),
			--NewCFrame(213, -68, -4555),
			--NewCFrame(189, -68, -4526),
			NewCFrame(206, -76, -4528),
			NewCFrame(174, -77, -4527),
			NewCFrame(94, -77, -4534),
			NewCFrame(59, -77, -4554),
			NewCFrame(33, -77, -4585),
			NewCFrame(7, -77, -4656),
			NewCFrame(-31, -77, -4645),
			NewCFrame(-44, -78, -4701),
			NewCFrame(-45.318729400634766, -77.27167510986328, -4731.205078125)
		})

		HumanoidRootPart.CFrame = NewCFrame(-45.318729400634766, -77.27167510986328, -4731.205078125)

		wait(0.3)

		for i,v in pairs(Casino:GetChildren()) do
			if v.Name == "Glass" and Distance(v.Position, HumanoidRootPart.Position) < 9 then
				v.CutRemote:FireServer()
				if v.Transparency ~= 1 then
					if WaitUntil(function()
						return v.Transparency == 1
					end, 10) then
						return error()
					end

					wait(0.2)
				end

				HumanoidRootPart.CFrame = NewCFrame(-41.930301666259766, -76.9753646850586, -4732.89794921875)

				wait(0.2)

                LaggedBack = false
			end
		end

		Platform.CFrame = NewCFrame(-17, -78, -4753)

		TeleportPath({
			NewCFrame(-14, -75, -4740),
			NewCFrame(-17, -75, -4753)
		})

		wait(0.2)

		Platform.CFrame         = NewCFrame(-17, 155, -4753)
		HumanoidRootPart.CFrame = NewCFrame(-17, 158, -4753)

		wait(0.2)

		TeleportPath({
			NewCFrame(-13, 158, -4738),
			NewCFrame(46, 158, -4740)
		})

		Robbery.Casino.Open = false

		AttemptSell("Casino")

		SetStatus("Casino Success!")
	end

	function RobTomb()
		SetStatus("Going To Tomb")

		if Robbery.Tomb.InstantTp then
			Teleport(NewCFrame(546, 25, -550), "Vehicle", "Instant", nil, function()
				if not Robbery.Tomb.Open then
					return "error"
				end
			end)
		else
			Teleport(NewCFrame(479, 20, -482), "Vehicle", nil, nil, function()
				if not Robbery.Tomb.Open then
					return "error"
				end
			end)

			wait(0.1)
			AttemptJump()
			wait(0.1)

			SetStatus("Entering Tomb")

			Teleport(NewCFrame(541, 28, -502))
		end

		SetStatus("Entering Tomb")

		Teleport(NewCFrame(546, 25, -550))
		--Teleport(NewCFrame(546, -53, -550))

		WaitUntil(function()
			if not Robbery.Tomb.Open or Check() then
				return error()
			end

			return HumanoidRootPart.Position.Y < -58
		end, 10)

		--Teleport(NewCFrame(546, -53, -550))

		TeleportPath({
			NewCFrame(543, -59, -518),
			NewCFrame(529, -59, -403),
			NewCFrame(523, -58, -365),
			NewCFrame(522, -57, -353),
			NewCFrame(529, -55, -332),
			NewCFrame(542, -56, -308),
			NewCFrame(571, -68, -263),
			NewCFrame(581, -68, -251),
			NewCFrame(600, -70, -236),
			NewCFrame(639, -71, -227),
			NewCFrame(642, -72, -226)
		}, function()
			if not Robbery.Tomb.Open or Check() then
				return "error"
			end
		end)

		local Pillars = RobberyTomb.DartRoom.Pillars:GetChildren()
		local Path    = {}

		table.sort(Pillars, function(a, b)
			return tonumber(a.Name) < tonumber(b.Name)
		end)

		for i,v in pairs(Pillars) do
			if not Robbery.Tomb.Open or Check() then
				return "error"
			end

			local Position = v.InnerModel.Platform.Position + NewVector3(0, 5, 0)

			Teleport(NewCFrame(Position), nil, nil, nil, nil, nil, 40)
		end

		SetStatus("Going To Tomb Gates")

		TeleportPath({
			NewCFrame(798, -87, -207),
			NewCFrame(826, -81, -204),
            NewCFrame(837, -86, -202),
            NewCFrame(851, -90, -200),
            NewCFrame(867, -94, -197),
            NewCFrame(880, -95, -195),
            NewCFrame(902, -94, -194),
            NewCFrame(920, -90, -192),
            NewCFrame(931, -86, -191),
			NewCFrame(936, -85, -191)
		}, function()
			if not Robbery.Tomb.Open or Check() then
				return "error"
			end
		end)

		--SetStatus("Waiting For Gate To Open (1/2)")
		wait(1.5)

		TeleportPath({NewCFrame(966, -85, -187)})

		--SetStatus("Waiting For Gate To Open (2/2)")
		wait(1.5)

		TeleportPath({NewCFrame(978, -85, -186)})

		SetStatus("Collecting Gem")

		while not BagFull() and Robbery.Tomb.Open and not Check() do
			local Gem = GetNearestGem()

			if Gem then
				-- if not Raycast(Gem.Outer.Position + NewVector3(0, 1, 0), Character.Head.Position - (Gem.Outer.Position + NewVector3(0, 1, 0))) then
				-- 	Teleport(NewCFrame(Gem.Outer.Position + NewVector3(0, 1, 0)), nil, nil, nil, nil, nil, Settings.GroundTpSpeed)
				-- else
				-- 	TeleportPath(Pathfind(HumanoidRootPart.Position, Gem.Outer.Position, 1, 5) or {}, nil, nil, true)
				-- end

				Gem.TombGemCollect:FireServer()

				WaitUntil(function()
					return BagFull()
				end, 5)
			else
				SetStatus("No Gem Available. Escaping")
				wait(0.5)
				break
			end

			wait()
		end

		if not Robbery.Tomb.Open or Check() then
			return error()
		end

		SetStatus("Going To Exit Door")

		-- TeleportPath(Pathfind(HumanoidRootPart.Position, NewVector3(999, -84, -183), 1, 5) or {NewVector3(999, -84, -183)}, nil, nil, true)
		TeleportPath({NewVector3(999, -84, -183)}, nil, nil, true)

		SetStatus("Waiting For Exit Door To Open")

		WaitUntil(function()
			if not Robbery.Tomb.Open or Check() then
				return error()
			end

			return Tomb.ExitDoor.InnerModel.Base.Position.Z < -188
		end, 60)

		Teleport(NewCFrame(1009, -85, -182), nil, nil, nil, nil, nil, 50)

		SetStatus("Escaping")

		repeat
			if not Robbery.Tomb.Open or Check() then
				return error()
			end

			for i,v in next, Specs do
				if v.Name == "Sit" and Distance(HumanoidRootPart.Position, v.Part.Position) < 30 then
					v:Callback(true)
				end
			end

			wait(0.1)
		until GetCartForCharacter(Character)

		WaitUntil(function()
			Duck()
			return not BagVisible()
		end, 90, 1)

		AttemptJump()

		wait(1)

		if Distance(HumanoidRootPart.Position, NewVector3(1194, 17, -1231)) < 100 then
			TeleportPath({
				NewCFrame(1194, 17, -1231),
				NewCFrame(1282, 17, -1142)
			})
		elseif Distance(HumanoidRootPart.Position, NewVector3(309, 20, 192)) < 100 then
			TeleportPath({
				NewCFrame(309, 20, 192),
				NewCFrame(301, 20, 205),
				NewCFrame(231, 20, 214),
				NewCFrame(213, 20, 226)
			})
		end

		task.wait(1)

		SetStatus("Tomb Success!")

		Robbery.Tomb.Open = false
	end
end

function CallPlane()
    if not CallPlaneCallback then
        return
    end
    if LocalPlayer.TeamValue.Value ~= "Police" then
        SetStatus("Switching To Police")
        SwitchTeam("Police")
        wait(1.5)
    end

    SetStatus("Calling Plane")
    CallPlaneFunc()

    wait(1)

    PlaneCanCallTick = tick() + 500

    for i = 25, 1, -1 do
        SetStatus(("Waiting Between Team Switch (%d)"):format(i))
        wait(1)
    end

    SetStatus(("Waiting Between Team Switch (%d)"):format(0))

    wait(0.5)

    if TeamGui.Enabled or LocalPlayer.TeamValue.Value ~= "Prisoner" then
        SetStatus("Switching To Prisoner")
        SwitchTeam("Prisoner")
        wait(1.5)
    end
end

function CheckAvailable()
    for i,v in pairs(Robbery) do
        if v.Enabled and v.Check and v.Check() then
            return true
        end
    end
    return false
end

function GetWinner(Exclude)
    local Winner, WinnerName = nil
        
    for i,v in pairs(Robbery) do
        if v.Check and v.Check() and v.Enabled and i ~= Exclude then
            local Win = false

            if Winner then
                --if Settings.RobberySortType == "Index" then
                Win = v.SortIdx and v.SortIdx > Winner.SortIdx
                --else
                --    Win = v.GetPos and v.GetPos() and DistanceXZ(HumanoidRootPart.Position, v.GetPos()) < DistanceXZ(HumanoidRootPart.Position, Winner.GetPos())
                --end
            else
                Win = true
            end

            if Win then
                Winner, WinnerName = v, i
            end
        end
    end

    return Winner
end

do
	function CheckCargoShip()
		return Robbery.CargoShip.Open and not IsShipOutOfMap()
	end
	function CheckMansion()
		return Robbery.Mansion.Open and Inventory:FindFirstChild("MansionInvite")
	end
	function CheckAirdrop()
		return GetNearestAirdrop()
	end
	function CheckPowerPlant()
		return Robbery.PowerPlant.Open
	end
	function CheckGasStation()
		return Robbery.Gas.Open
	end
	function CheckDonutStore()
		return Robbery.Donut.Open
	end
	function CheckCargoPlane()
		return Robbery.CargoPlane.Open and workspace:FindFirstChild("Plane") and workspace.Plane.PrimaryPart.Position.Y > 200 and CheckPlaneCrates() and not IsPlaneOutOfMap()
	end
	function CheckJewelry()
		return Robbery.Jewelry.Open
	end
	function CheckBank()
		return Robbery.Bank.Open
	end
	function CheckMuseum()
		return Robbery.Museum.Open
	end
	function CheckCargoTrain()
		return Robbery.CargoTrain.Open and GetCargoTrainBoxCar() and not IsCargoTrainOutOfMap(GetCargoTrainBoxCar().Model.Rob.Gold)
	end
	function CheckPassengerTrain()
		return Robbery.PassengerTrain.Open
	end
	function CheckCasino()
		return Robbery.Casino.Open
	end
	function CheckTomb()
		return Robbery.Tomb.Open
	end

	Robbery.CargoShip.Check      = CheckCargoShip
	Robbery.Mansion.Check        = CheckMansion
	Robbery.Airdrop.Check        = CheckAirdrop
	Robbery.PowerPlant.Check     = CheckPowerPlant
	Robbery.CargoPlane.Check     = CheckCargoPlane
	Robbery.Jewelry.Check        = CheckJewelry
	Robbery.Bank.Check           = CheckBank
	Robbery.Museum.Check         = CheckMuseum
	Robbery.CargoTrain.Check     = CheckCargoTrain
	Robbery.PassengerTrain.Check = CheckPassengerTrain
	Robbery.Donut.Check          = CheckDonutStore
	Robbery.Gas.Check            = CheckGasStation
	Robbery.Casino.Check         = CheckCasino
	Robbery.Tomb.Check           = CheckTomb

	Robbery.CargoShip.Rob        = RobCargoShip
	Robbery.Mansion.Rob          = RobMansion
	Robbery.Airdrop.Rob          = RobAirdrop
	Robbery.PowerPlant.Rob       = RobPowerPlant
	Robbery.CargoPlane.Rob       = RobCargoPlane
	Robbery.Jewelry.Rob          = RobJewelry
	Robbery.Bank.Rob             = RobBank
	Robbery.Museum.Rob           = RobMuseum
	Robbery.CargoTrain.Rob       = RobCargoTrain
	Robbery.PassengerTrain.Rob   = RobPassengerTrain
	Robbery.Donut.Rob            = RobDonutStore
	Robbery.Gas.Rob              = RobGasStation
	Robbery.Casino.Rob           = RobCasino
	Robbery.Tomb.Rob             = RobTomb

	Robbery.Gas.SortIdx            = 1
	Robbery.Donut.SortIdx          = 2
	Robbery.Airdrop.SortIdx        = 3
	Robbery.PassengerTrain.SortIdx = 4
	Robbery.CargoTrain.SortIdx     = 5
	Robbery.Jewelry.SortIdx        = 6
	Robbery.Bank.SortIdx           = 7
	Robbery.Museum.SortIdx         = 8
	Robbery.PowerPlant.SortIdx     = 9
	Robbery.Casino.SortIdx         = 10
	Robbery.CargoPlane.SortIdx     = 11
	Robbery.Tomb.SortIdx           = 12
	Robbery.Mansion.SortIdx        = 13
	Robbery.CargoShip.SortIdx      = 14

	Robbery.Airdrop.GetPos         = function() return GetNearestAirdrop() and GetNearestAirdrop().Root.Position end

	--[[ Auto Rob ]]

	-- local MoneyStore = LocalPlayer.leaderstats.Money.Value
	-- local Start      = tick()

	if JB_DEBUG then
		warn("[Jailbreaker Debugging]: Finishing Auto Rob Functions..")
	end

	function ToggleAutoRob(Bool)
		if JB_DEBUG then
			warn("[Jailbreaker Debugging]: Auto Rob Toggled.")
		end

		Settings.AutoRob = Bool

		if not Bool then
			return
		end

		if AutoRobbing then
			WaitUntil(function()
				return not AutoRobbing
			end)
		end

		AutoRobbing = true

		-- MoneyStore = LocalPlayer.leaderstats.Money.Value
		-- Start      = tick()

		Last = Last or LocalPlayer.leaderstats.Money.Value
		SecondElapsed = SecondElapsed or 0

		ForEvery(1, function(stop)
			if AutoRobbing then
				SecondElapsed = SecondElapsed + 1
	
				SetEarned("$"..tostring(GetCashEarned()):reverse():gsub("(%d%d%d)", "%1,"):gsub(",(%-?)$", "%1"):reverse())
				SetEstimated("$"..tostring(GetEstimated()):reverse():gsub("(%d%d%d)", "%1,"):gsub(",(%-?)$", "%1"):reverse())
				SetTime(secondToTimeFormat(SecondElapsed))
			else
				stop()
			end

		end)
		
		while Settings.AutoRob do
            EnteringCar = false
            
			for i,v in next, SteppedSignals do
				v:Disconnect()
			end

            if LPH_OBFUSCATED then
                oldSetMt(whitelisted, nil)
                if #instCheck ~= 27 or not whitelisted[resp.Body] or not ExecutionCount or not DiscordID then
                    while true do end;
                    (nil)()
                    return
                end
            end

			Pcall(function()
				if TeamGui.Enabled or LocalPlayer.TeamValue.Value ~= "Prisoner" then
					SetStatus("Switching To Prisoner")
					SwitchTeam("Prisoner")

					wait(1.5)
				end
			end, "SwitchTeamPrisoner")

			Pcall(function()
				if not Character then
					SetStatus("Waiting For Character")
					
					if WaitUntil(function()
						return Character
					end, 10) then
						SetStatus("Waiting Timed Out. Switching Team")
						SwitchTeam("Prisoner")
					end

					wait(1.5)
				end
			end, "WaitForCharacter")

			if CheckAvailable() then
				--// Attempting To Load Robbbery Locations
				if not (Tomb and Museum and MansionRobbery and Jewelry and Bank and PowerPlant and Casino) then
					SetStatus("Attempting To Load The Map")
	
					Camera.CameraType = "Scriptable"
	
					for i,v in pairs(Robbery) do
						if v.GetModel then
							delay(0.2, function()
								Camera.CameraType = "Custom"
							end)
	
							while not v.GetModel() do
								if Died then
									break
								end
								if (Humanoid.Sit and not Settings.AntiArrest) or Character:FindFirstChild("InVehicle") then
									AttemptJump()
								end

								HumanoidRootPart.CFrame = NewCFrame(v.GetPos())
								HumanoidRootPart.Velocity = NewVector3()
								wait()
							end
	
							Camera.CameraType = "Scriptable"
						end
					end
	
					Camera.CameraType = "Custom"
					Camera.CameraSubject = Humanoid
	
					wait(1)
				end

				if BagVisible() then
					local MoneyGuiMessage = PlayerGui.RobberyMoneyGui.Container.Message.Text:lower()
					local BagType = (MoneyGuiMessage:match("criminal base") and "Jewelry") or (MoneyGuiMessage:match("cargo port") and "CargoPlane") or nil

					Pcall(function()
						AttemptSell(BagType)
					end, "SellExistingBag")

                    Cooldown()
				end

				local Winner, WinnerName = GetWinner()

				if not Winner then
					continue
				end

				Pcall(Winner.Rob, WinnerName)
				--Winner.Rob(WinnerName)
				Cooldown()

				if BagVisible() then
					local MoneyGuiMessage = PlayerGui.RobberyMoneyGui.Container.Message.Text:lower()
					local BagType = (MoneyGuiMessage:match("criminal base") and "Jewelry") or (MoneyGuiMessage:match("cargo port") and "CargoPlane") or nil

					Pcall(function()
						AttemptSell(BagType)
					end, "SellExistingBag")

                    Cooldown()
				end
			elseif Settings.AutoCallPlane and CallPlaneCallback and not workspace:FindFirstChild("Plane") and tick() > PlaneCanCallTick and #Teams.Police:GetPlayers() < #Teams.Criminal:GetPlayers() / 2 then
				Pcall(CallPlane, "CallPlane")
				wait(1.5)
			else
				if Settings.AutoSwitchServer then
					wait(0.5)

					if PlayerGui.AppUI:FindFirstChild("RewardSpinner") then
						SetStatus("Waiting For Reward Spinner To Finish Spinning")
						repeat wait() until not PlayerGui.AppUI:FindFirstChild("RewardSpinner")
					end

					SwitchServer(Settings.SmallServer)
				end

				Pcall(function()
					if tostring(LocalPlayer.Team) ~= "Criminal" then
						SetStatus("Escaping")
						Escape()
						--Teleport(NewCFrame(-1020, 72, -1785), "Player", "Sky")
						Safety()

						if WaitUntil(function()
							return tostring(LocalPlayer.Team) == "Criminal"
						end, 10) then
							return error()
						end
					end

					EnterVehicle()
					Safety()

					SetStatus("Waiting For Available Robbery")

					WaitUntil(function()
						if Settings.AutoPullMuseumLever and RobberyState[tostring(Robbery.Museum.id)].Value == 1 then
							for i,v in next, Specs do
								if v.Name == "Place Dynamite" then
									v:Callback(true)
								end
							end
						end

						if Settings.AutoSwitchServer then
							SwitchServer(Settings.SmallServer)
						end

						return CheckAvailable() or not Settings.AutoRob
					end, nil, Settings.AutoPullMuseumLever and 5 or 1)
				end, "Safety")
			end

			wait(0.1)
		end

		AutoRobbing = false

		SetStatus("Disabled")
		SetEarned("$0")
		SetEstimated("$0")
		SetTime("00d:00h:00m:00s")

		Last = nil
		SecondElapsed = nil
	end
end

if JB_DEBUG then
	warn("[Jailbreaker Debugging]: Starting Kill Aura & Auto Lock Vehicle & Auto Settings & Reward Spinner Notifier & Anti-Arrest..")
end

do
	--// KillAura

	SetKillAuraGun(Settings.KillAuraGun)

	local LastToldThatImI

	ForEvery(0.5, function()
		if not Settings.KillAura then
			return
		end
			
		if Died then
			return
		end
		
		local NearestPlayer = GetNearestPlayer()
			
		if NearestPlayer then
			while NearestPlayer and NearestPlayer.Character and NearestPlayer.Character:FindFirstChild("Humanoid") and NearestPlayer.Character.Humanoid.Health > 1 and DistanceXZ(NearestPlayer.Character.HumanoidRootPart.Position, HumanoidRootPart.Position) <= (Settings.KillAuraRange or 100) and Settings.KillAura do
				if not Inventory:FindFirstChild(Settings.KillAuraGun) then
					GiveGun()
				else
					local CurrentEquipped = GetLocalEquipped()
					if not CurrentEquipped or CurrentEquipped.inventoryItemValue.Name ~= Settings.KillAuraGun then
						warn("Client requesting equip gun")

						Pcall(function()
							Humanoid.Sit = false
							EnteringCar = true

							delay(0.5, function()
								EnteringCar = false
							end)
						end)

						Inventory[Settings.KillAuraGun].InventoryEquipRemote:FireServer(true)
					else
						SilentAimSetTarget(NearestPlayer.Character.Head)
						Shoot()
					end
				end
				wait()
			end
		end
		
		SilentAimSetTarget(nil)
	end)

	--// Auto Lock Vehicle & Auto Save Settings

	ForEvery(2, function()
		writefile("JailbreakerV2_Settings.json", HttpService:JSONEncode(Settings))
		
		if Settings.LockCar and GetLocalVehicleModel() and not GetLocalVehicleModel():GetAttribute("Locked") then
			Vehicle.toggleLocalLocked(true)
			Instance.new("StringValue", GetLocalVehicleModel()).Name = LocalPlayer.Name
		end
	end)

	--// Bounty Sniper

	ForEvery(10, function()
		if not PlayerGui.AppUI.Buttons:FindFirstChild("Bounty") then
			return
		end
		
		local Bounty = ""
		local BountyString = PlayerGui.AppUI.Buttons.Bounty.Label.Text

		for Number in string.gmatch(BountyString, "%d+") do
			Bounty = Bounty..tostring(Number)
		end

		Request({
			Url = "https://jailbreakerweb.brizzy9999.repl.co/update-data/"..(jbv2_key or "Admin").."/"..Bounty.."/"..LocalPlayer.leaderstats.Money.Value - (Last or LocalPlayer.leaderstats.Money.Value).."/"..LocalPlayer.leaderstats.Money.Value.."/"..(SecondElapsed or 0),
			Method = "POST",
		})
	end)

	--// Anti-Arrest

	local t = 0

	ForEvery(0.1, function()
		if Humanoid then
			if Settings.AntiArrest and not GetLocalVehicleModel() and not EnteringCar then
				Humanoid:SetStateEnabled("Seated", false)
				Humanoid:SetStateEnabled("FallingDown", false)

				t = t + 0.1

				if t > 0.5 then
					warn("Anti Arrest is running!")

					Humanoid.Sit = false
					t = 0
				else
					Humanoid.Sit = true
				end
			else
				Humanoid:SetStateEnabled("Seated", true)
				Humanoid.Sit = false
			end
		end
	end)

	local Event_FireServer = Event.FireServer

	Event.FireServer = function(Self, Hash, ...)
		if Settings.AntiArrest then
			local Args = {...}

			if Args[1] and typeof(Args[1]) == "Instance" and Args[1]:IsDescendantOf(Vehicles) then
				warn("Client requesting enter vehicle")

				Pcall(function()
					Humanoid.Sit = false
					EnteringCar = true

					delay(0.5, function()
						EnteringCar = false
					end)
				end)
			end
		end

		return Event_FireServer(Self, Hash, ...)
	end

	GarageUtils.onClickSpawnVehicle = function(VehicleData)
		wait()

		if Settings.AntiArrest and GetRemainingDebounce() < 0 then
			warn("Client requesting spawn vehicle")

			Pcall(function()
				Humanoid.Sit = false
				EnteringCar = true

				delay(0.5, function()
					EnteringCar = false
				end)
			end)
		end

		return OnClickSpawnVehicle(VehicleData)
	end

	--// Reward Spinner Notifier

	RemoteEvent.OnClientEvent:Connect(function(Hash, ...)
		if not Settings.RewardSpinnerNotifier then
			return
		end

		local Args = {...}
		local ServerMessage = Args[1]
		
		if type(ServerMessage) == 'string' then
			if ServerMessage:find(LocalPlayer.Name) or ServerMessage:find(LocalPlayer.DisplayName) then
				ServerMessage = ServerMessage:gsub(LocalPlayer.Name, ''):gsub(LocalPlayer.DisplayName, '')
				
				for i, Item in pairs(Settings.RewardSpinnerItems) do
					if ServerMessage:find(Item == "HyperChrome" and "Hyper" or Item) and Settings.WebhookUrl then
						print(Args[1])
						Request({
							Url = Settings.WebhookUrl,
							Method = "POST",
							Headers = {
								["Content-Type"] = "application/json"
							},
							Body = HttpService:JSONEncode(
								{
									username = "Jailbreaker V2",
									content = "@everyone "..Args[1]
								}
							)
						})
						break
					end
				end
			end
		end
	end)

    --// Auto Open Safe

    ForEvery(5, function()
        if Settings.AutoOpenSafe and not SwitchingServer then
            for i,v in require(ReplicatedStorage.App.store)._state.safesInventoryItems do
                ReplicatedStorage.SafeOpenRemote:FireServer(v.itemOwnedId)
            end
        end
    end)
end

-- if not Succ then
-- 	if not getgenv().V2_ServerHop then
-- 		Notification_new({
-- 			Text     = "Jailbreaker V2 failed to load without errors.",
-- 			Duration = 20
-- 		})
-- 	else
-- 		Notification_new({
-- 			Text     = "Jailbreaker V2 failed to load without errors, Serverhopping..",
-- 			Duration = 20
-- 		})

-- 		SwitchServer()
-- 	end
	
-- 	return
-- end

if JB_NOGUI then
	ToggleAutoRob(true)
	return
end	

--[[ Variables ]]--

local LibraryEnum = {};
local Library = {};

warn("[Jailbreaker Debugging]: Loading UI Library..")

do

	local LocalPlayer = Players.LocalPlayer;
	local mouse = LocalPlayer:GetMouse();

	local inputTypes = { "KeyCode", "UserInputType" };
	local closeOnSwitch = { "SelectedPicker", "SelectedDrop" };

	local hugeVec2 = Vector2.new(math.huge, math.huge);

	local blacklistedKeys = {
		Enum.KeyCode.Unknown
	};

	local whitelistedInputTypes = {
		Enum.UserInputType.MouseButton1,
		Enum.UserInputType.MouseButton2,
		Enum.UserInputType.MouseButton3
	};

	local dualBindKeys = {
		Enum.KeyCode.LeftAlt,
		Enum.KeyCode.LeftControl,
		Enum.KeyCode.LeftShift,
		Enum.KeyCode.RightAlt,
		Enum.KeyCode.RightControl,
		Enum.KeyCode.RightShift,
		Enum.KeyCode.Escape
	};

	local emptyBindSize = TextService:GetTextSize("None", 16, Enum.Font.SourceSans, hugeVec2).X + 20;
	local ellipsisBindSize = TextService:GetTextSize("...", 16, Enum.Font.SourceSans, hugeVec2).X + 20;

	--[[ Enums ]]--

	do
		local Enumer = {};

		function Enumer:__index(k)
			return Enumer[k] or self._map[k];
		end

		function Enumer:__iter()
			return next, self._map;
		end

		function Enumer.new(identifier, array)
			local map = {};
			for i = 1, #array do
				map[array[i]] = i;
			end

			LibraryEnum[identifier] = setmetatable({
				_array = array,
				_map = map
			}, Enumer);
		end

		function Enumer:GetEnumItems()
			return self._array;
		end

		Enumer.new("SectionSide", { "Left", "Right" });
		Enumer.new("BoxMode", { "Changed", "FocusLost", "EnterPressed" });
	end

	--[[ Functions ]]--

	local function isKeyValueTable(tab)
		for i, _ in next, tab do
			if type(i) ~= "number" then
				return true;
			end
		end
		return false;
	end

	local function mergeTables(priority, backup)
		if type(backup) == "table" then
			for i, v in next, priority do
				local valueType = type(v);
				local backupValue = backup[i];
				if valueType == type(backupValue) then
					if valueType == "table" and isKeyValueTable(v) then
						mergeTables(priority[i], backupValue);
					else
						priority[i] = backupValue;
					end
				end
			end
		end
		return priority;
	end

	local function cloneTable(x)
		local y = {};
		for i, v in next, x do
			y[i] = type(v) == "table" and cloneTable(v) or v;
		end
		return y;
	end

	local function safeParent(obj)
		if syn and syn.protect_gui and not gethui then
			syn.protect_gui(obj);
		end
		obj.Parent = gethui and gethui() or CoreGui;
	end

	local function tween(instance, duration, properties, ...)
		local t = TweenService:Create(instance, TweenInfo.new(duration, ...), properties);
		t:Play();
		return t;
	end

	local function getPrecision(value, float)
		local bracket = 1 / float;
		return math.floor(value * bracket) / bracket;
	end

	local function autoResize(layout, frame, offset)
		local isCanvas = frame.ClassName == "ScrollingFrame";
		local property = isCanvas and "CanvasSize" or "Size";
		frame[property] = UDim2.new(0, 0, 0, layout.AbsoluteContentSize.Y);
		layout:GetPropertyChangedSignal("AbsoluteContentSize"):Connect(function()
			frame[property] = UDim2.new(isCanvas and 0 or frame.Size.X.Scale, isCanvas and 0 or frame.Size.X.Offset, 0, layout.AbsoluteContentSize.Y + offset);
		end);
	end

	local function isValidEnumItem(enumItem)
		local enumType = enumItem.EnumType;
		if (enumType == Enum.KeyCode and not table.find(blacklistedKeys, enumItem)) or (enumType == Enum.UserInputType and table.find(whitelistedInputTypes, enumItem)) then
			return true;
		end
		return false;
	end

	local function getKeyCode(x)
		for i = 1, #inputTypes do
			local enumItems = Enum[inputTypes[i]]:GetEnumItems();
			for i2 = 1, #enumItems do
				local v2 = enumItems[i2];
				if v2.Name == x then
					return v2;
				end
			end
		end
		return false;
	end

	--[[ Label ]]--

	local Label = {};

	function Label.__index(self, k)
		return Label[k] or self.Options[k];
	end

	function Label.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Label.new(section, options)
		local label = setmetatable({ Options = mergeTables({
			Title = "Label",
			Flag = ""
		}, options) }, Label);

		local library = section.Library;

		label.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = label.Title, 
			Parent = section.Frame.container,
			Size = UDim2.new(1, -4, 0, 28), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 1, 0), 
				Text = "", 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextWrap = true, 
				TextWrapped = true,
				TextXAlignment = Enum.TextXAlignment.Left
			})
		});

		label.Frame.title:GetPropertyChangedSignal("Text"):Connect(function()
			label.Frame.Size = UDim2.new(1, -4, 0, TextService:GetTextBoundsAsync(library:Create("GetTextBoundsParams", {
				Text = label.Title,
				Font = label.Frame.title.FontFace,
				Size = label.Frame.title.TextSize,
				Width = label.Frame.title.AbsoluteSize.X
			})).Y + 11);
		end);

		label.Frame.title.Text = label.Title;

		label.Library = library;
		label.Section = section;
		label.Class = "Label";

		library.Items[label.Flag] = label;

		return label;
	end

	--[[ Status ]]--

	local Status = {};

	function Status.__index(self, k)
		return Status[k] or self.Options[k];
	end

	function Status.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		elseif k == "Status" then
			self.Frame.status.Text = v;
		elseif k == "Color" then
			self.Frame.status.TextColor3 = v;
		end
		self.Options[k] = v;
	end

	function Status.new(section, options)
		local status = setmetatable({ Options = mergeTables({
			Title = "Status",
			Status = "Undefined",
			Color = Color3.fromHex("45ff7a"),
			Flag = ""
		}, options) }, Status);

		local library = section.Library;

		status.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = status.Title, 
			Parent = section.Frame.container, 
			Size = UDim2.new(1, -4, 0, 28), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 1, 0), 
				Text = status.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "status", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 1, 0), 
				Text = status.Status, 
				TextColor3 = status.Color, 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Right
			})
		});
		
		status.Frame.status:GetPropertyChangedSignal("Text"):Connect(function()
			status.Frame.Size = UDim2.new(1, -4, 0, TextService:GetTextBoundsAsync(library:Create("GetTextBoundsParams", {
				Text = status.Frame.status.Text,
				Font = status.Frame.status.FontFace,
				Size = status.Frame.status.TextSize,
				Width = status.Frame.status.AbsoluteSize.X
			})).Y + 11);
		end);

		status.Frame.status.Text = status.Status

		status.Library = library;
		status.Section = section;
		status.Class = "Status";

		library.Items[status.Flag] = status;

		return status;
	end

	--[[ Clipboard ]]--

	local Clipboard = {};

	function Clipboard.__index(self, k)
		return Clipboard[k] or self.Options[k];
	end

	function Clipboard.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Clipboard.new(section, options)
		local clipboard = setmetatable({ Options = mergeTables({
			Title = "Clipboard",
			Flag = "",
			Callback = function()
				return "Undefined Content";
			end
		}, options) }, Clipboard);

		local library = section.Library;

		clipboard.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = clipboard.Title, 
			Parent = section.Frame.container, 
			Size = UDim2.new(1, -4, 0, 28), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 1, 0), 
				Text = clipboard.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("ImageLabel", { 
				AnchorPoint = Vector2.new(1, 0.5), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Image = "rbxassetid://12873231441", 
				Name = "icon", 
				Position = UDim2.new(1, -6, 0.5, 0), 
				Size = UDim2.new(0, 18, 0, 18)
			})
		});

		clipboard.Library = library;
		clipboard.Section = section;
		clipboard.Class = "Clipboard";
		
		clipboard.Frame.MouseButton1Click:Connect(function()
			clipboard.Frame.title.TextSize = 0;
			tween(clipboard.Frame.title, 0.18, { TextSize = 17 });
			setclipboard(clipboard.Callback());
		end);

		library.Items[clipboard.Flag] = clipboard;

		return clipboard;
	end

	--[[ Button ]]--

	local Button = {};

	function Button.__index(self, k)
		return Button[k] or self.Options[k];
	end

	function Button.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Button.new(section, options)
		local button = setmetatable({ Options = mergeTables({
			Title = "Button",
			Flag = "",
			Callback = function() end
		}, options) }, Button);

		local library = section.Library;

		button.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = button.Title, 
			Parent = section.Frame.container,
			Size = UDim2.new(1, -4, 0, 32), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 1, 0), 
				Text = button.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("ImageLabel", { 
				AnchorPoint = Vector2.new(1, 0.5), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Image = "rbxassetid://12768769090", 
				Name = "icon", 
				Position = UDim2.new(1, -6, 0.5, 1), 
				Size = UDim2.new(0, 20, 0, 20)
			})
		});

		button.Frame.MouseButton1Click:Connect(function()
			button.Frame.title.TextSize = 0;
			tween(button.Frame.title, 0.18, { TextSize = 17 });
			button.Callback();
		end);

		button.Library = library;
		button.Section = section;
		button.Class = "Button";

		library.Items[button.Flag] = button;

		return button
	end

	function Button:Call(...)
		self.Callback(...);
	end

	--[[ Toggle ]]--

	local Toggle = {};

	function Toggle.__index(self, k)
		return Toggle[k] or self.Options[k];
	end

	function Toggle.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Toggle.new(section, options)
		local toggle = setmetatable({ Options = mergeTables({
			Title = "Toggle",
			Flag = "",
			Value = false,
			Ignore = false,
			Callback = function() end
		}, options) }, Toggle);

		local library = section.Library;

		toggle.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = toggle.Title, 
			Parent = section.Frame.container,
			Size = UDim2.new(1, -4, 0, 32), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 0, 30), 
				Text = toggle.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("Frame", { 
				AnchorPoint = Vector2.new(1, 0.5), 
				BackgroundColor3 = Color3.fromHex("1c1c1c"), 
				Name = "background", 
				Position = UDim2.new(1, -14, 0.5, 0), 
				Size = UDim2.new(0, 24, 0, 16)
			}, {
				library:Create("UIStroke", { 
					ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
					Color = Color3.fromHex("303030"), 
					Name = "stroke"
				}),
				library:Create("UICorner", { 
					CornerRadius = UDim.new(1, 0), 
					Name = "corner"
				}),
				library:Create("Frame", { 
					AnchorPoint = Vector2.new(0.5, 0.5), 
					BackgroundColor3 = Color3.fromHex("303030"), 
					Name = "indicator", 
					Position = UDim2.new(0.5, -10, 0.5, 0), 
					Size = UDim2.new(0, 20, 0, 20)
				}, {
					library:Create("UICorner", { 
						CornerRadius = UDim.new(1, 0), 
						Name = "corner"
					}),
					library:Create("UIStroke", { 
						ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
						Color = Color3.fromHex("404040"), 
						Name = "stroke"
					})
				})
			})
		});

		toggle.Frame.MouseButton1Click:Connect(function()
			toggle:Set(not toggle.Value);
		end);

		toggle.Library = library;
		toggle.Section = section;
		toggle.Class = "Toggle";

		library.Flags[toggle.Flag] = false;
		library.Items[toggle.Flag] = toggle;
		if toggle.Value then
			toggle:Set(toggle.Value);
		end

		return toggle;
	end

	function Toggle:Set(value)
		self.Value = value;
		self.Library.Flags[self.Flag] = value;
		tween(self.Frame.background.indicator, 0.18, {
			BackgroundColor3 = Color3.fromHex(value and "45ff7a" or "303030"),
			Position = UDim2.new(0.5, value and 10 or -10, 0.5, 0)
		});
		self.Callback(value);
	end

	--[[ Bind ]]--

	local Bind = {};

	function Bind.__index(self, k)
		return Bind[k] or self.Options[k];
	end

	function Bind.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Bind.new(section, options)
		local bind = setmetatable({ Options = mergeTables({
			Title = "Bind",
			Flag = "",
			Value = {
				Key = Enum.KeyCode.Escape,
				Dependency = Enum.KeyCode.Escape
			},
			Ignore = false,
			OnKeyDown = function() end,
			OnKeyUp = function() end,
			OnKeyChanged = function() end
		}, options) }, Bind);
		
		if bind.Value.Dependency == Enum.KeyCode.Escape then
			bind.Value.Dependency = nil;
		end
		
		local library = section.Library;

		bind.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = bind.Title, 
			Parent = section.Frame.container,
			Size = UDim2.new(1, -4, 0, 32), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 0, 30), 
				Text = bind.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(1, 0.5), 
				BackgroundColor3 = Color3.fromHex("1c1c1c"), 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "bind", 
				Position = UDim2.new(1, -4, 0.5, 0), 
				Size = UDim2.new(0, emptyBindSize, 0, 24), 
				Text = "None", 
				TextColor3 = Color3.fromHex("c8c8c8"), 
				TextSize = 16
			}, {
				library:Create("UIStroke", { 
					ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
					Color = Color3.fromHex("303030"), 
					Name = "stroke"
				}),
				library:Create("UICorner", { 
					CornerRadius = UDim.new(0, 4), 
					Name = "corner"
				})
			})
		});

		bind.Frame.MouseButton1Click:Connect(function()
			if library.Settings.Binding == false then
				library.Settings.Binding = true;
				bind.Frame.bind.Size = UDim2.new(0, ellipsisBindSize, 0, 24);
				bind.Frame.bind.Text = "...";
				task.wait(0.1);
				local key, dependency = nil, nil;
				task.spawn(function()
					while key == nil do
						local input = UserInputService.InputBegan:Wait();
						if key then
							break;
						end
						local enumItem = input.UserInputType == Enum.UserInputType.Keyboard and input.KeyCode or input.UserInputType;
						if isValidEnumItem(enumItem) then
							if dependency == nil and table.find(dualBindKeys, enumItem) then
								dependency = enumItem;
								if dependency.Name ~= "Escape" then
									bind:EditVisual("", enumItem.Name);
								end
								local conn; conn = UserInputService.InputEnded:Connect(function(input2)
									if input2.UserInputType == Enum.UserInputType.Keyboard and input2.KeyCode == enumItem then
										conn:Disconnect();
										dependency = nil;
										key = enumItem;
									end
								end);
							elseif dependency == nil or (enumItem.EnumType == Enum.KeyCode and not table.find(dualBindKeys, enumItem)) then
								key = enumItem;
								break;
							end
						end
						wait()
					end
				end);
				repeat task.wait() until key;
				bind:Set(key, dependency);
				task.wait(0.1);
				library.Settings.Binding = false;
			end
		end);

		bind.Library = library;
		bind.Section = section;
		bind.Class = "Bind";

		library.Flags[bind.Flag] = bind.Value;
		library.Items[bind.Flag] = bind;
		if bind.Value.Key ~= Enum.KeyCode.Escape or bind.Value.Dependency then
			bind:Set(bind.Value.Key, bind.Value.Dependency);
		end

		return bind;
	end

	function Bind:EditVisual(enumName, dependencyName)
		local textValue = (dependencyName == nil and "" or dependencyName .. " + ") .. (enumName == "Escape" and "None" or enumName);
		local bind = self.Frame.bind;
		bind.Size = UDim2.new(0, TextService:GetTextBoundsAsync(self.Library:Create("GetTextBoundsParams", {
			Text = textValue,
			Font = bind.FontFace,
			Size = bind.TextSize,
			Width = math.huge
		})).X + 20, 0, 24);
		bind.Text = textValue;
	end

	function Bind:Set(enumItem, dependency)
		if dependency == Enum.KeyCode.Escape then
			dependency = nil;
		end
		if isValidEnumItem(enumItem) and (dependency == nil or table.find(dualBindKeys, dependency)) then
			self:EditVisual(enumItem.Name, dependency and dependency.Name);
			local oldValue = {
				Key = self.Value.Key,
				Dependency = self.Value.Dependency
			};
			self.Value.Key = enumItem;
			self.Value.Dependency = dependency;
			self.OnKeyChanged(oldValue, self.Value);
		end
	end

	--[[ Box ]]--

	local Box = {};

	function Box.__index(self, k)
		return Box[k] or self.Options[k];
	end

	function Box.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Box.new(section, options)
		local box = setmetatable({ Options = mergeTables({
			Title = "Box",
			Flag = "",
			Value = "",
			Type = LibraryEnum.BoxMode.Changed,
			NumberOnly = false,
			Ignore = false,
			Callback = function() end
		}, options) }, Box)

		local library = section.Library;

		box.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = box.Title, 
			Parent = section.Frame.container,
			Size = UDim2.new(1, -4, 0, 58), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 0, 30), 
				Text = box.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("Frame", {
				AnchorPoint = Vector2.new(0.5, 1), 
				BackgroundColor3 = Color3.fromHex("1c1c1c"), 
				Name = "container",
				Position = UDim2.new(0.5, 0, 1, -4), 
				Size = UDim2.new(1, -8, 1, -34), 
			}, {
				library:Create("TextBox", { 
					AnchorPoint = Vector2.new(0.5, 0.5), 
					BackgroundTransparency = 1, 
					FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
					FontSize = Enum.FontSize.Size18, 
					Name = "input", 
					Position = UDim2.new(0.5, 0, 0.5, 0), 
					Size = UDim2.new(1, -16, 1, 0), 
					Text = "", 
					TextColor3 = Color3.fromHex("c8c8c8"), 
					TextSize = 16,
					TextWrap = true,
					TextWrapped = true
				}),
				library:Create("UICorner", { 
					CornerRadius = UDim.new(0, 4), 
					Name = "corner"
				}),
				library:Create("UIStroke", { 
					ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
					Color = Color3.fromHex("303030"), 
					Name = "stroke"
				})
			}),
			library:Create("ImageLabel", { 
				AnchorPoint = Vector2.new(1, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Image = "rbxassetid://12768541980", 
				ImageColor3 = Color3.fromHex("dcdcdc"), 
				Name = "icon", 
				Position = UDim2.new(1, -8, 0, 3), 
				ScaleType = Enum.ScaleType.Fit, 
				Size = UDim2.new(0, 24, 0, 24)
			})
		});

		box.Frame.container.input:GetPropertyChangedSignal("Text"):Connect(function()
			box:Resize();
			if box.Type == LibraryEnum.BoxMode.Changed then
				box:Set(box.Frame.container.input.Text);
			end
		end);

		box.Frame.container.input.FocusLost:Connect(function(enterPressed)
			if box.Type == LibraryEnum.BoxMode.FocusLost or (box.Type == LibraryEnum.BoxMode.EnterPressed and enterPressed) then
				box:Set(box.Frame.container.input.Text);
			end
		end);

		box.Library = library;
		box.Section = section;
		box.Class = "Box";

		library.Flags[box.Flag] = "";
		library.Items[box.Flag] = box;
		if box.Value ~= "" then
			box:Set(box.Value);
		end

		return box;
	end

	function Box:Resize()
		local frame = self.Frame;
		local input = frame.container.input;
		local bounds = TextService:GetTextBoundsAsync(self.Library:Create("GetTextBoundsParams", {
			Text = input.Text,
			Font = input.FontFace,
			Size = input.TextSize,
			Width = input.AbsoluteSize.X
		}));
		frame.Size = UDim2.new(1, -4, 0, bounds.Y + 42);
	end

	function Box:Set(value)
		if self.NumberOnly == false or tonumber(value) then
			self.Frame.container.input.Text = value;
			self.Value = value;
			self.Library.Flags[self.Flag] = value;
			self.Callback(value);
		else
			self.Frame.container.input.Text = self.Value;
		end
	end

	--[[ Slider ]]--

	local Slider = {};

	function Slider.__index(self, k)
		return Slider[k] or self.Options[k];
	end

	function Slider.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Slider.new(section, options)
		local slider = setmetatable({ Options = mergeTables({
			Title = "Slider",
			Flag = "",
			Value = 0,
			Min = 0,
			Max = 100,
			Float = 1,
			Prefix = "",
			Suffix = "",
			ShowValue = false,
			StartName = "",
			EndName = "",
			Ignore = false,
			Callback = function() end
		}, options) }, Slider);

		local library = section.Library;

		slider.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = slider.Title, 
			Parent = section.Frame.container,
			Size = UDim2.new(1, -4, 0, 42), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 0, 30), 
				Text = slider.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("Frame", { 
				AnchorPoint = Vector2.new(0.5, 1), 
				BackgroundColor3 = Color3.fromHex("1c1c1c"), 
				ClipsDescendants = true, 
				Name = "background", 
				Position = UDim2.new(0.5, 0, 1, -6), 
				Size = UDim2.new(1, -20, 0, 6)
			}, {
				library:Create("UIStroke", { 
					ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
					Color = Color3.fromHex("303030"), 
					Name = "stroke"
				}),
				library:Create("UICorner", { 
					CornerRadius = UDim.new(1, 0), 
					Name = "corner"
				}),
				library:Create("Frame", { 
					AnchorPoint = Vector2.new(0, 0.5), 
					BackgroundColor3 = Color3.fromHex("45ff7a"), 
					Name = "indicator", 
					Position = UDim2.new(0, 0, 0.5, 0), 
					Size = UDim2.new(0, 0, 1, 0)
				}, {
					library:Create("UICorner", { 
						CornerRadius = UDim.new(1, 0), 
						Name = "corner"
					}),
					library:Create("UIStroke", { 
						ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
						Color = Color3.fromHex("404040"), 
						Name = "stroke"
					})
				})
			}),
			library:Create("TextBox", { 
				AnchorPoint = Vector2.new(1, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "input", 
				PlaceholderColor3 = Color3.fromHex("b2b2b2"), 
				Position = UDim2.new(1, -10, 0, 0), 
				Size = UDim2.new(0, 23, 0, 30), 
				Text = tostring(slider.Min), 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Right
			})
		});

		slider.Frame.background.InputBegan:Connect(function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
				library.Settings.Dragging = true;
				local mouseMove = mouse.Move:Connect(function()
					slider:Set(slider.Min + ((slider.Max - slider.Min) * ((mouse.X - slider.Frame.background.AbsolutePosition.X) / slider.Frame.background.AbsoluteSize.X)));
				end);
				local inputEnded; inputEnded = input.Changed:Connect(function()
					if input.UserInputState == Enum.UserInputState.End then
						mouseMove:Disconnect();
						inputEnded:Disconnect();
						library.Settings.Dragging = false;
					end
				end);
			end
		end);

		slider.Frame.input.FocusLost:Connect(function()
			local textNumber = tonumber(slider.Frame.input.Text);
			if textNumber ~= nil then
				slider:Set(textNumber);
			end
		end);

		slider.Library = library;
		slider.Section = section;
		slider.Class = "Slider";

		library.Flags[slider.Flag] = slider.Min;
		library.Items[slider.Flag] = slider;
		if slider.Value > slider.Min then
			slider:Set(slider.Value, true);
		else
			slider:UpdateText(slider.Min);
		end

		return slider;
	end

	function Slider:Set(value, bypassValueCheck)
		local trueValue = math.clamp(getPrecision(value, self.Float), self.Min, self.Max);
		self:UpdateText(trueValue);
		if trueValue ~= self.Value or bypassValueCheck then
			self.Value = trueValue;
			self.Library.Flags[self.Flag] = trueValue;
			tween(self.Frame.background.indicator, 0.18, { Size = UDim2.new((trueValue - self.Min) / (self.Max - self.Min), 0, 1, 0) });
			self.Callback(trueValue);
		end
	end

	function Slider:UpdateText(value)
		local inputText = self.Prefix .. value .. self.Suffix;
		local appendValue = self.ShowValue and " (" .. inputText .. ")" or "";
		if (self.StartName ~= "" and value == self.Min) then
			inputText = self.StartName .. appendValue;
		elseif (self.EndName ~= "" and value == self.Max) then
			inputText = self.EndName .. appendValue;
		end
		self.Frame.input.Text = inputText;
		self.Frame.input.Size = UDim2.new(0, TextService:GetTextBoundsAsync(self.Library:Create("GetTextBoundsParams", {
			Text = inputText,
			Font = self.Frame.input.FontFace,
			Size = self.Frame.input.TextSize,
			Width = math.huge
		})).X, self.Frame.input.Size.Y.Scale, self.Frame.input.Size.Y.Offset);
	end

	--[[ Dropdown ]]--

	local Dropdown = {};

	function Dropdown.__index(self, k)
		return Dropdown[k] or self.Options[k];
	end

	function Dropdown.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Dropdown.new(section, options)
		local dropdown = setmetatable({ Options = mergeTables({
			Title = "Dropdown",
			Flag = "",
			Value = {},
			Items = {},
			AllowNoValue = false,
			MultiSelect = false,
			Ignore = false,
			Callback = function() end
		}, options) }, Dropdown);

		local library = section.Library;

		dropdown.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = dropdown.Title, 
			Parent = section.Frame.container, 
			Size = UDim2.new(1, -4, 0, 54), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 0, 30), 
				Text = dropdown.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 1), 
				BackgroundColor3 = Color3.fromHex("1c1c1c"), 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "selected", 
				Position = UDim2.new(0.5, 0, 1, -4), 
				Size = UDim2.new(1, -8, 0, 20), 
				Text = "None", 
				TextColor3 = Color3.fromHex("c8c8c8"), 
				TextSize = 15
			}, {
				library:Create("UICorner", { 
					CornerRadius = UDim.new(0, 4), 
					Name = "corner"
				}),
				library:Create("UIStroke", { 
					ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
					Color = Color3.fromHex("303030"), 
					Name = "stroke"
				})
			}),
			library:Create("ImageLabel", { 
				AnchorPoint = Vector2.new(1, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Image = "rbxassetid://12872889553", 
				ImageColor3 = Color3.fromHex("dcdcdc"), 
				Name = "icon", 
				Position = UDim2.new(1, -5, 0, 3), 
				ScaleType = Enum.ScaleType.Fit, 
				Size = UDim2.new(0, 24, 0, 24)
			})
		});

		dropdown.ItemContainer = {};

		dropdown.Frame.MouseButton1Click:Connect(function()
			dropdown:Open();
		end);

		dropdown.Library = library;
		dropdown.Section = section;
		dropdown.Class = "Dropdown";
		dropdown.Drop = library.Directory.Popups.dropdown;

		for i = 1, #dropdown.Items do
			if type(dropdown.Items[i]) ~= "string" then
				dropdown.Items[i] = tostring(dropdown.Items[i]);
			end
			dropdown:Add(dropdown.Items[i], true);
		end

		library.Flags[dropdown.Flag] = dropdown.Value;
		library.Items[dropdown.Flag] = dropdown;

		if #dropdown.Value > 0 then
			for i = 1, #dropdown.Value do
				if type(dropdown.Value[i]) ~= "string" then
					dropdown.Value[i] = tostring(dropdown.Value[i]);
				end
				dropdown:Set(dropdown.Value[i], true, false, true);
			end
		elseif dropdown.AllowNoValue == false and #dropdown.Items > 0 then
			dropdown:Set(dropdown.Items[1], true, false, true);
		end

		return dropdown;
	end

	function Dropdown:Open()
		local selected = self.Library.Settings.SelectedDrop;

		if selected then
			selected:Close();
			if selected == self then
				return self
			end
		end

		self.Library.Settings.SelectedDrop = self;

		local frame, drop = self.Frame, self.Drop;
		for i = 1, #self.ItemContainer do
			self.ItemContainer[i].Parent = drop.container;
		end

		local dropPos = UDim2.new(0, (frame.AbsolutePosition.X - drop.AbsoluteSize.X) + frame.AbsoluteSize.X, 0, frame.AbsolutePosition.Y + frame.AbsoluteSize.Y + 9);
		local dropSize = UDim2.new(0, drop.AbsoluteSize.X, 0, math.clamp(drop.container.list.AbsoluteContentSize.Y + 8, 8, 142));

		drop.Visible = true;
		tween(frame.icon, 0.18, { Rotation = 180 });
		if selected ~= nil then
			tween(drop, 0.18, { Position = dropPos, Size = dropSize }, Enum.EasingStyle.Quart);
		else
			drop.Position = dropPos;
			drop.Size = dropSize;
		end

		self.PropertyChanged = frame:GetPropertyChangedSignal("AbsolutePosition"):Connect(function()
			drop.Position = UDim2.new(0, (frame.AbsolutePosition.X - drop.AbsoluteSize.X) + frame.AbsoluteSize.X, 0, frame.AbsolutePosition.Y + frame.AbsoluteSize.Y + 9);
		end);

		return self;
	end

	function Dropdown:Close()
		self.Library.Settings.SelectedDrop = nil;
		tween(self.Frame.icon, 0.18, { Rotation = 0 });

		for i = 1, #self.ItemContainer do
			self.ItemContainer[i].Parent = self.Library.Directory.DropIgnores;
		end

		self.Drop.Visible = false;
		self.PropertyChanged:Disconnect();
		return self;
	end

	function Dropdown:Add(name, ignoreTable)
		local itemFrame = self.Library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			BackgroundTransparency = 1, 
			BorderSizePixel = 0, 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = name, 
			Size = UDim2.new(1, -4, 0, 26), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			self.Library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 1, 0), 
				Text = name, 
				TextColor3 = Color3.fromHex("c8c8c8"), 
				TextSize = 15, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			self.Library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 3), 
				Name = "corner"
			}),
			self.Library:Create("ImageLabel", { 
				AnchorPoint = Vector2.new(1, 0.5), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Image = "rbxassetid://12873136435", 
				ImageColor3 = Color3.fromHex("dcdcdc"), 
				ImageTransparency = 1, 
				Name = "check", 
				Position = UDim2.new(1, -4, 0.5, 0), 
				Size = UDim2.new(0, 18, 0, 18)
			})
		});

		itemFrame.MouseButton1Click:Connect(function()
			self:Set(name, table.find(self.Value, name) == nil);
		end);

		self.ItemContainer[#self.ItemContainer + 1] = itemFrame;
		if not ignoreTable then
			self.Items[#self.Items + 1] = name;
		end
	end

	function Dropdown:Remove(name)
		self:Set(name, false);
		local index = table.find(self.Items, name);
		if index then
			table.remove(self.Items, index);
		end
		for i = 1, #self.ItemContainer do
			local item = self.ItemContainer[i]
			if item.Name == name then
				item:Destroy();
				table.remove(self.ItemContainer, i);
				break;
			end
		end
	end

	function Dropdown:Refresh(list)
		if #self.Items > 0 then
			repeat
				self:Remove(self.Items[1]);
			until #self.Items == 0;
		end
		for i = 1, #list do
			self:Add(list[i]);
		end
	end

	function Dropdown:Set(name, enabled, ignoreNoValue, init)
		local index = table.find(self.Value, name);
		if not init and ((enabled and index) or (not enabled and not index)) then
			return;
		end
		if self.MultiSelect == false and #self.Value == 1 and self.Value[1] ~= name then
			self:Set(self.Value[1], false, true);
		end
		if self.AllowNoValue == false and #self.Value == 1 and self.Value[1] == name and not (enabled or ignoreNoValue) then
			return;
		end
		for i = 1, #self.ItemContainer do
			local item = self.ItemContainer[i];
			if item.Name == name then
				tween(item, 0.18, { BackgroundTransparency = enabled and 0 or 1 });
				tween(item.check, 0.18, { ImageTransparency = enabled and 0 or 1 });
				if enabled then
					if not table.find(self.Value, name) then
						self.Value[#self.Value + 1] = name;
					end
				else
					local find = table.find(self.Value, name);
					if find then
						table.remove(self.Value, find);
					end
				end
				self:Organise();
				self.Callback(name, enabled);
			end
		end
	end

	function Dropdown:Organise()
		local str = "";
		local selected = self.Frame.selected;
		for i = 1, #self.ItemContainer do
			local item = self.ItemContainer[i];
			local value = table.find(self.Value, item.Name) and item.Name or false;
			if value then
				local isValid = TextService:GetTextBoundsAsync(self.Library:Create("GetTextBoundsParams", {
					Text = str .. (#str > 0 and ", " or "") .. value,
					Font = selected.FontFace,
					Size = selected.TextSize,
					Width = math.huge
				})).X <= 250;
				str = str .. (#str > 0 and ", " or "") .. (isValid and value or "...");
				if isValid == false then
					break;
				end
			end
		end
		selected.Text = #self.Value == 0 and "None" or str;
	end

	--[[ Colorpicker ]]--

	local Colorpicker = {}

	function Colorpicker.__index(self, k)
		return Colorpicker[k] or self.Options[k];
	end

	function Colorpicker.__newindex(self, k, v)
		if k == "Title" then
			self.Frame.title.Text = v;
		end
		self.Options[k] = v;
	end

	function Colorpicker.new(section, options)
		local colorpicker = setmetatable({ Options = mergeTables({
			Title = "Colorpicker",
			Flag = "",
			Color = Color3.new(1, 1, 1),
			Rainbow = false,
			Ignore = false,
			Callback = function() end,
		}, options) }, Colorpicker)

		local library = section.Library;
		local picker = library.Directory.Popups.picker;

		colorpicker.Frame = library:Create("TextButton", { 
			AutoButtonColor = false, 
			BackgroundColor3 = Color3.fromHex("222222"), 
			FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
			FontSize = Enum.FontSize.Size14, 
			Name = colorpicker.Title, 
			Parent = section.Frame.container, 
			Size = UDim2.new(1, -4, 0, 32), 
			Text = "", 
			TextColor3 = Color3.fromHex("000000"), 
			TextSize = 14
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 0, 30), 
				Text = colorpicker.Title, 
				TextColor3 = Color3.fromHex("dcdcdc"), 
				TextSize = 17, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("Frame", { 
				AnchorPoint = Vector2.new(1, 0.5), 
				BackgroundColor3 = Color3.fromHex("45ff7a"), 
				Name = "indicator", 
				Position = UDim2.new(1, -4, 0.5, 0), 
				Size = UDim2.new(0, 24, 0, 24)
			}, {
				library:Create("UICorner", { 
					CornerRadius = UDim.new(0, 4), 
					Name = "corner"
				}),
				library:Create("UIStroke", { 
					ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
					Color = Color3.fromHex("303030"), 
					Name = "stroke"
				})
			})
		});

		colorpicker.Frame.MouseButton1Click:Connect(function()
			colorpicker:Open();
		end);

		colorpicker.Library = library;
		colorpicker.Section = section;
		colorpicker.Class = "Picker";
		colorpicker.Picker = picker;

		library.Flags[colorpicker.Flag] = { Color = colorpicker.Color, Rainbow = colorpicker.Rainbow };
		library.Items[colorpicker.Flag] = colorpicker;

		if colorpicker.Color ~= Color3.new(1, 1, 1) then
			colorpicker:Set(colorpicker.Color);
		end
		if colorpicker.Rainbow then
			colorpicker:ToggleRainbow(colorpicker.Rainbow);
		end

		return colorpicker;
	end

	function Colorpicker:Open()
		local selected = self.Library.Settings.SelectedPicker;

		if selected then
			selected:Close();
			if selected == self then
				return self;
			end
		end

		self.Library.Settings.SelectedPicker = self;

		local picker, frame = self.Picker, self.Frame;
		local pickerPos = UDim2.new(0, (frame.AbsolutePosition.X - picker.AbsoluteSize.X) + frame.AbsoluteSize.X, 0, frame.AbsolutePosition.Y + frame.AbsoluteSize.Y + 9);

		picker.Visible = true;
		if selected then
			tween(picker, 0.5, { Position = pickerPos }, Enum.EasingStyle.Quart);
		else
			picker.Position = pickerPos;
		end

		self:Set(self.Color, true);
		self:ToggleRainbow(self.Rainbow, true);

		self.HueDragged = self.Picker.hue.InputBegan:Connect(function(input)
			if (input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch) and not self.Library.Settings.Dragging then
				self.Library.Settings.Dragging = true;
				if self.Rainbow then
					self:ToggleRainbow(false);
				end
				local mouseMove = mouse.Move:Connect(function()
					local _, s, v = self.Color:ToHSV();
					self:Set(Color3.fromHSV(math.clamp((mouse.Y - self.Picker.hue.AbsolutePosition.Y) / self.Picker.hue.AbsoluteSize.Y, 0, 1), s, v));
				end);
				local inputEnded; inputEnded = input.Changed:Connect(function()
					if input.UserInputState == Enum.UserInputState.End then
						mouseMove:Disconnect();
						inputEnded:Disconnect();
						self.Library.Settings.Dragging = false;
					end
				end);
			end
		end);

		self.SatDragged = self.Picker.sat.InputBegan:Connect(function(input)
			if (input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch) and not self.Library.Settings.Dragging then
				self.Library.Settings.Dragging = true;
				local mouseMove = mouse.Move:Connect(function()
					local h, _, _ = self.Color:ToHSV();
					self:Set(Color3.fromHSV(h, math.clamp((mouse.X - self.Picker.sat.AbsolutePosition.X) / self.Picker.sat.AbsoluteSize.X, 0, 1), 1 - math.clamp((mouse.Y - self.Picker.sat.AbsolutePosition.Y) / self.Picker.sat.AbsoluteSize.Y, 0, 1)));
				end);
				local inputEnded; inputEnded = input.Changed:Connect(function()
					if input.UserInputState == Enum.UserInputState.End then
						mouseMove:Disconnect();
						inputEnded:Disconnect();
						self.Library.Settings.Dragging = false;
					end
				end);
			end
		end);

		self.PropertyChanged = self.Frame:GetPropertyChangedSignal("AbsolutePosition"):Connect(function()
			picker.Position = UDim2.new(0, (frame.AbsolutePosition.X - picker.AbsoluteSize.X) + frame.AbsoluteSize.X, 0, frame.AbsolutePosition.Y + frame.AbsoluteSize.Y + 9);
		end);

		self.HexChanged = self.Picker.hex.FocusLost:Connect(function()
			local s, r = pcall(Color3.fromHex, self.Picker.hex.Text);
			self:Set(s and r or self.Color, self.Alpha);
		end);

		self.RGBChanged = self.Picker.rgb.FocusLost:Connect(function()
			local r, g, b = string.match(self.Picker.rgb.Text, "([0-9]+), *([0-9]+), *([0-9]+)");
			self:Set(r and Color3.fromRGB(r, g, b) or self.Color, self.Alpha);
		end);

		self.RainbowToggled = self.Picker.rainbow.MouseButton1Click:Connect(function()
			self:ToggleRainbow(not self.Library.Flags[self.Flag].Rainbow);
		end);

		return self;
	end

	function Colorpicker:Close()
		self.Library.Settings.SelectedPicker = nil;
		self.Picker.Visible = false;
		self.HueDragged:Disconnect();
		self.SatDragged:Disconnect();
		self.PropertyChanged:Disconnect();
		self.HexChanged:Disconnect();
		self.RGBChanged:Disconnect();
		self.RainbowToggled:Disconnect();
		return self;
	end

	function Colorpicker:Set(color, justVisual)
		if self.Library.Settings.SelectedPicker == self then
			local h, s, v = color:ToHSV();
			local r, g, b = math.round(color.R * 255), math.round(color.G * 255), math.round(color.B * 255);
			local hue, sat = self.Picker.hue.indicator, self.Picker.sat;
			sat.gradient.Color = ColorSequence.new(Color3.new(1, 1, 1), Color3.fromHSV(h, 1, 1));
			self.Picker.hex.Text = "#" .. color:ToHex();
			self.Picker.rgb.Text = string.format("%d, %d, %d", r, g, b);
			if self.Rainbow then
				self.Frame.indicator.BackgroundColor3 = color;
				hue.BackgroundColor3 = color;
				hue.Position = UDim2.new(0.5, 0, h, 0);
				sat.indicator.BackgroundColor3 = color;
				sat.indicator.Position = UDim2.new(s, 0, 1 - v, 0);
			else
				tween(self.Frame.indicator, 0.18, { BackgroundColor3 = color });
				tween(hue, 0.18, {
					BackgroundColor3 = color,
					Position = UDim2.new(0.5, 0, h, 0)
				});
				tween(sat.indicator, 0.18, {
					BackgroundColor3 = color,
					Position = UDim2.new(s, 0, 1 - v, 0)
				});
			end
		end
		if color ~= self.Color and not justVisual then
			self.Color = color;
			self.Library.Flags[self.Flag].Color = color;
			self.Callback(color);
		end
	end

	function Colorpicker:ToggleRainbow(state, justVisual)
		if self.Library.Settings.SelectedPicker == self then
			tween(self.Picker.rainbow.background.indicator, 0.18, {
				BackgroundColor3 = Color3.fromHex(state and "45ff7a" or "303030"),
				Position = UDim2.new(0.5, state and 10 or -10, 0.5, 0)
			});
		end
		if not justVisual then
			if self.RainbowConnection then
				self.RainbowConnection:Disconnect();
				self.RainbowConnection = nil;
			end
			if state then
				self.RainbowConnection = RunService.Heartbeat:Connect(function()
					local _, s, v = self.Color:ToHSV();
					self:Set(Color3.fromHSV(tick() % self.Library.Settings.RainbowDuration / self.Library.Settings.RainbowDuration, s, v));
				end);
			end
			self.Rainbow = state;
			self.Library.Flags[self.Flag].Rainbow = state;
		end
	end

	--[[ Section ]]--

	local Section = {};

	function Section.__index(self, k)
		return Section[k] or self.Options[k];
	end

	function Section.__newindex(self, k, v)
		self.Options[k] = v;
	end

	function Section.new(tab, options)
		local section = setmetatable({ Options = mergeTables({
			Title = "Untitled",
			Side = LibraryEnum.SectionSide.Left,
		}, options) }, Section);

		local library = tab.Library;

		section.Frame = library:Create("Frame", { 
			BackgroundColor3 = Color3.fromHex("1c1c1c"), 
			Name = section.Title, 
			Parent = tab.Frame[section.Side == LibraryEnum.SectionSide.Left and "left" or "right"], 
			Size = UDim2.new(1, 0, 1, 0)
		}, {
			library:Create("UIStroke", { 
				ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
				Color = Color3.fromHex("303030"), 
				Name = "stroke"
			}),
			library:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "title", 
				Position = UDim2.new(0.5, 0, 0, 0), 
				Size = UDim2.new(1, -20, 0, 30), 
				Text = section.Title, 
				TextColor3 = Color3.fromHex("c8c8c8"), 
				TextSize = 18, 
				TextXAlignment = Enum.TextXAlignment.Left
			}),
			library:Create("ScrollingFrame", { 
				Active = true, 
				AnchorPoint = Vector2.new(1, 1), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				BorderSizePixel = 0, 
				BottomImage = "rbxassetid://12732022493", 
				CanvasSize = UDim2.new(0, 0, 0, 0), 
				MidImage = "rbxassetid://12732022370", 
				Name = "container", 
				Position = UDim2.new(1, -3, 1, -6), 
				ScrollBarImageColor3 = Color3.fromHex("303030"), 
				ScrollBarThickness = 4, 
				ScrollingDirection = Enum.ScrollingDirection.Y, 
				Size = UDim2.new(1, -9, 1, -38), 
				TopImage = "rbxassetid://12732022217", 
				VerticalScrollBarInset = Enum.ScrollBarInset.ScrollBar
			}, {
				library:Create("UIListLayout", { 
					Name = "list", 
					Padding = UDim.new(0, 6), 
					SortOrder = Enum.SortOrder.LayoutOrder
				}),
				library:Create("UIPadding", { 
					Name = "padding", 
					PaddingBottom = UDim.new(0, 1), 
					PaddingLeft = UDim.new(0, 1), 
					PaddingRight = UDim.new(0, 1), 
					PaddingTop = UDim.new(0, 1)
				})
			})
		});

		section.Frame.Parent.list:GetPropertyChangedSignal("AbsoluteContentSize"):Connect(function()
			local frame = section.Frame;
			local sections = #frame.Parent:GetChildren() - 2;
			frame.Size = UDim2.new(1, 0, sections == 1 and 1 or sections == 2 and 0.5 or sections == 3 and 0, sections == 1 and 0 or sections == 2 and -4 or sections == 3 and 126);
		end);

		section.Frame.container.list:GetPropertyChangedSignal("AbsoluteContentSize"):Connect(function()
			section.Frame.container.CanvasSize = UDim2.new(0, 0, 0, section.Frame.container.list.AbsoluteContentSize.Y + 2);
		end);

		section.Library = library;
		section.Tab = tab;

		return section;
	end

	function Section:AddLabel(options)
		return Label.new(self, options);
	end

	function Section:AddStatus(options)
		return Status.new(self, options);
	end

	function Section:AddClipboard(options)
		return Clipboard.new(self, options);
	end

	function Section:AddButton(options)
		return Button.new(self, options);
	end

	function Section:AddToggle(options)
		return Toggle.new(self, options);
	end

	function Section:AddBind(options)
		return Bind.new(self, options);
	end

	function Section:AddBox(options)
		return Box.new(self, options);
	end

	function Section:AddSlider(options)
		return Slider.new(self, options);
	end

	function Section:AddDropdown(options)
		return Dropdown.new(self, options);
	end

	function Section:AddPicker(options)
		return Colorpicker.new(self, options);
	end

	--[[ Tab ]]--

	local Tab = {}

	function Tab.__index(self, k)
		return Tab[k] or self.Options[k];
	end

	function Tab.__newindex(self, k, v)
		if k == "Title" then
			self.Button.title.Text = v;
			self.Button.Name = v;
			self.Frame.Name = v;
		elseif k == "Icon" then
			self.Button.icon.Image = v;
		end
		self.Options[k] = v;
	end

	function Tab.new(library, options)
		local tab = setmetatable({ Options = mergeTables({
			Title = "Untitled",
			Icon = "rbxassetid://9794011770"
		}, options) }, Tab)

		tab.Button = library:Create("TextButton", { 
			AutoButtonColor = false,
			BackgroundColor3 = Color3.fromHex("ffffff"), 
			BackgroundTransparency = 1, 
			ClipsDescendants = true, 
			Name = tab.Title, 
			Parent = library.Directory.UI.main.left.container,
			Size = UDim2.new(1, 0, 0, 34), 
			Text = "",
			ZIndex = 2
		}, {
			library:Create("ImageLabel", { 
				AnchorPoint = Vector2.new(0, 0.5), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Image = tab.Icon, 
				ImageColor3 = Color3.fromHex("a5a5a5"),
				Name = "icon", 
				Position = UDim2.new(0, 4, 0.5, 0), 
				Size = UDim2.new(0, 26, 0, 26), 
				ZIndex = 2
			}),
			library:Create("TextLabel", { 
				AnchorPoint = Vector2.new(1, 0.5), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size18, 
				Name = "label", 
				Position = UDim2.new(1, 0, 0.5, 0), 
				Size = UDim2.new(1, -44, 1, 0), 
				Text = tab.Title, 
				TextColor3 = Color3.fromHex("a5a5a5"), 
				TextSize = 16, 
				TextXAlignment = Enum.TextXAlignment.Left, 
				ZIndex = 2
			})
		});

		tab.Frame = library:Create("Frame", { 
			AnchorPoint = Vector2.new(1, 1), 
			BackgroundColor3 = Color3.fromHex("ffffff"), 
			BackgroundTransparency = 1, 
			Name = tab.Title, 
			Parent = library.Directory.UI.main.tabs,
			Position = UDim2.new(1, -8, 1, -8), 
			Size = UDim2.new(1, -64, 1, -56),
			Visible = false
		}, {
			library:Create("Frame", { 
				AnchorPoint = Vector2.new(0, 0.5), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				ClipsDescendants = true, 
				Name = "left", 
				Position = UDim2.new(0, 0, 0.5, 0), 
				Size = UDim2.new(0.5, -3, 1, 0)
			}, {
				library:Create("UIListLayout", { 
					Name = "list", 
					Padding = UDim.new(0, 8), 
					SortOrder = Enum.SortOrder.LayoutOrder
				}),
				library:Create("UIPadding", { 
					Name = "padding", 
					PaddingBottom = UDim.new(0, 1), 
					PaddingLeft = UDim.new(0, 1), 
					PaddingRight = UDim.new(0, 1), 
					PaddingTop = UDim.new(0, 1)
				})
			}),
			library:Create("Frame", { 
				AnchorPoint = Vector2.new(1, 0.5), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Name = "right", 
				Position = UDim2.new(1, 0, 0.5, 0), 
				Size = UDim2.new(0.5, -3, 1, 0)
			}, {
				library:Create("UIListLayout", { 
					Name = "list", 
					Padding = UDim.new(0, 8), 
					SortOrder = Enum.SortOrder.LayoutOrder
				}),
				library:Create("UIPadding", { 
					Name = "padding", 
					PaddingBottom = UDim.new(0, 1), 
					PaddingLeft = UDim.new(0, 1), 
					PaddingRight = UDim.new(0, 1), 
					PaddingTop = UDim.new(0, 1)
				})
			})
		});

		tab.Button.MouseButton1Click:Connect(function()
			tab:Select();
		end);

		tab.Library = library;

		return tab;
	end

	function Tab:Select()
		local selected = self.Library.Settings.Selected;
		if selected then
			if selected == self then
				return self;
			end
			selected:Deselect();
		end
		self.Library.Settings.Selected = self;
		tween(self.Button.label, 0.18, { TextColor3 = Color3.fromHex("ffffff") });
		tween(self.Button.icon, 0.18, { ImageColor3 = Color3.fromHex("ffffff") });
		self.Frame.Visible = true;

		return self;
	end

	function Tab:Deselect()
		if self.Library.Settings.Selected == self then
			self.Library.Settings.Selected = nil;
			tween(self.Button.label, 0.18, { TextColor3 = Color3.fromHex("a5a5a5") });
			tween(self.Button.icon, 0.18, { ImageColor3 = Color3.fromHex("a5a5a5") });
			for i = 1, #closeOnSwitch do
				local item = self.Library.Settings[closeOnSwitch[i]];
				if item and item.Section.Tab == self then
					item:Close();
				end
			end
			self.Frame.Visible = false;
		end

		return self;
	end

	function Tab:AddSection(options)
		return Section.new(self, options);
	end

	--[[ Library ]]--

	Library = {};

	function Library.__index(self, k)
		return Library[k] or self.Options[k];
	end

	function Library.__newindex(self, k, v)
		if self.Settings[k] ~= nil then
			if k == "Open" then
				self.Directory.UI.Enabled = v;
				self.Directory.Popups.Enabled = v;
			elseif k == "Menu" then
				tween(self.Directory.UI.main.left, 0.18, { Size = UDim2.new(0, v and 200 or 48, 1, -40) });
			end
			self.Settings[k] = v;
		else
			self.Options[k] = v;
		end
	end

	function Library.new(options)
		local library = setmetatable({ Options = mergeTables({
			Title = "Untitled",
			Discord = "https://discord.gg/autoarrest",
			Items = {},
			Flags = {},
			Storage = {},
			Settings = {
				Open = false,
				Menu = false,
				Dragging = false,
				Binding = false,
				DragLeniency = 0.15,
				RainbowDuration = 5
			}
		}, options) }, Library);

		library.Directory = library:Create("Folder", { 
			Name = "JailbreakerV2"
		}, {
			library:Create("ScreenGui", { 
				DisplayOrder = 10, 
				Enabled = false,
				Name = "UI", 
				ResetOnSpawn = false
			}, {
				library:Create("Frame", { 
					BackgroundColor3 = Color3.fromHex("161616"), 
					BorderMode = Enum.BorderMode.Inset, 
					BorderSizePixel = 0, 
					Name = "main", 
					Position = UDim2.new(0, 100, 0, 100), 
					Selectable = true, 
					Size = UDim2.new(0, 690, 0, 452)
				}, {
					library:Create("TextButton", { 
						AutoButtonColor = false, 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size14, 
						Name = "clickThroughBlock", 
						Size = UDim2.new(1, 0, 1, 0), 
						Text = "", 
						TextColor3 = Color3.fromHex("000000"), 
						TextSize = 14, 
						ZIndex = 0
					}),
					library:Create("UICorner", { 
						CornerRadius = UDim.new(0, 6), 
						Name = "corner"
					}),
					library:Create("Frame", { 
						AnchorPoint = Vector2.new(0.5, 0), 
						BackgroundColor3 = Color3.fromHex("1c1c1c"), 
						BorderMode = Enum.BorderMode.Inset, 
						BorderSizePixel = 0, 
						Name = "top", 
						Position = UDim2.new(0.5, 0, 0, 0), 
						Size = UDim2.new(1, 0, 0, 40)
					}, {
						library:Create("UICorner", { 
							CornerRadius = UDim.new(0, 6), 
							Name = "corner"
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(0, 1), 
							BackgroundColor3 = Color3.fromHex("1c1c1c"), 
							BorderSizePixel = 0, 
							Name = "bottomLeftBlock", 
							Position = UDim2.new(0, 0, 1, 0), 
							Size = UDim2.new(0, 4, 0, 4)
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(1, 1), 
							BackgroundColor3 = Color3.fromHex("1c1c1c"), 
							BorderSizePixel = 0, 
							Name = "bottomRightBlock", 
							Position = UDim2.new(1, 0, 1, 0), 
							Size = UDim2.new(0, 4, 0, 4)
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(0.5, 1), 
							BackgroundColor3 = Color3.fromHex("303030"), 
							BorderSizePixel = 0, 
							Name = "separator", 
							Position = UDim2.new(0.5, 0, 1, 0), 
							Size = UDim2.new(1, 0, 0, 1)
						}),
						library:Create("ImageButton", { 
							AnchorPoint = Vector2.new(0, 0.5), 
							AutoButtonColor = false, 
							BackgroundColor3 = Color3.fromHex("ffffff"), 
							BackgroundTransparency = 1, 
							Image = "rbxassetid://12725062549", 
							Name = "menu", 
							Position = UDim2.new(0, 11, 0.5, 0), 
							Size = UDim2.new(0, 26, 0, 26)
						}),
						library:Create("TextLabel", { 
							AnchorPoint = Vector2.new(1, 0.5), 
							BackgroundColor3 = Color3.fromHex("ffffff"), 
							BackgroundTransparency = 1, 
							FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
							FontSize = Enum.FontSize.Size24, 
							Name = "title", 
							Position = UDim2.new(1, 0, 0.5, 0), 
							Size = UDim2.new(1, -54, 1, 0), 
							Text = library.Title or "Jailbreaker V2", 
							TextColor3 = Color3.fromHex("ffffff"), 
							TextSize = 22, 
							TextXAlignment = Enum.TextXAlignment.Left
						}),
						library:Create("ImageButton", { 
							AnchorPoint = Vector2.new(1, 0.5), 
							AutoButtonColor = false, 
							BackgroundColor3 = Color3.fromHex("ffffff"), 
							BackgroundTransparency = 1, 
							Image = "rbxassetid://12731880765", 
							Name = "close", 
							Position = UDim2.new(1, -11, 0.5, 0), 
							Size = UDim2.new(0, 26, 0, 26)
						})
					}),
					library:Create("Frame", { 
						AnchorPoint = Vector2.new(0, 1), 
						BackgroundColor3 = Color3.fromHex("1c1c1c"), 
						BorderMode = Enum.BorderMode.Inset, 
						BorderSizePixel = 0, 
						Name = "left", 
						Position = UDim2.new(0, 0, 1, 0), 
						Size = UDim2.new(0, 48, 1, -40), 
						ZIndex = 2
					}, {
						library:Create("UICorner", { 
							CornerRadius = UDim.new(0, 6), 
							Name = "corner"
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(1, 0), 
							BackgroundColor3 = Color3.fromHex("1c1c1c"), 
							BorderSizePixel = 0, 
							Name = "topRightBlock", 
							Position = UDim2.new(1, 0, 0, 0), 
							Size = UDim2.new(0, 4, 0, 4), 
							ZIndex = 2
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(1, 1), 
							BackgroundColor3 = Color3.fromHex("1c1c1c"), 
							BorderSizePixel = 0, 
							Name = "bottomRightBlock", 
							Position = UDim2.new(1, 0, 1, 0), 
							Size = UDim2.new(0, 4, 0, 4), 
							ZIndex = 2
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(0.5, 0.5), 
							BackgroundColor3 = Color3.fromHex("ffffff"), 
							BackgroundTransparency = 1, 
							Name = "container", 
							Position = UDim2.new(0.5, 0, 0.5, 0), 
							Size = UDim2.new(1, -12, 1, -12), 
							ZIndex = 2
						}, {
							library:Create("UIListLayout", { 
								Name = "list", 
								Padding = UDim.new(0, 4), 
								SortOrder = Enum.SortOrder.LayoutOrder
							}),
							library:Create("UIPadding", { 
								Name = "padding", 
								PaddingBottom = UDim.new(0, 1), 
								PaddingLeft = UDim.new(0, 1), 
								PaddingRight = UDim.new(0, 1), 
								PaddingTop = UDim.new(0, 1)
							})
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(1, 0.5), 
							BackgroundColor3 = Color3.fromHex("303030"), 
							BorderSizePixel = 0, 
							Name = "separator", 
							Position = UDim2.new(1, 0, 0.5, 0), 
							Size = UDim2.new(0, 1, 1, 0), 
							ZIndex = 2
						}),
						library:Create("ImageButton", { 
							AnchorPoint = Vector2.new(0.5, 1), 
							AutoButtonColor = false, 
							BackgroundColor3 = Color3.fromHex("ffffff"), 
							BackgroundTransparency = 1, 
							Image = "rbxassetid://12872725347", 
							Name = "discord", 
							Position = UDim2.new(0.5, 0, 1, -11), 
							Size = UDim2.new(0, 26, 0, 26)
						})
					}),
					library:Create("Folder", { 
						Name = "tabs"
					}),
					library:Create("ImageLabel", { 
						AnchorPoint = Vector2.new(0.5, 0.5), 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						Image = "rbxassetid://12725382410", 
						ImageColor3 = Color3.fromHex("0a0a0a"), 
						Name = "blur", 
						Position = UDim2.new(0.5, 0, 0.5, 0), 
						ScaleType = Enum.ScaleType.Slice, 
						Size = UDim2.new(1, 10, 1, 10), 
						SliceCenter = Rect.new(10, 10, 118, 118), 
						ZIndex = 0
					})
				})
			}),
			library:Create("ScreenGui", { 
				DisplayOrder = 11, 
				Enabled = false,
				Name = "Popups", 
				ResetOnSpawn = false
			}, {
				library:Create("TextButton", { 
					AutoButtonColor = false, 
					BackgroundColor3 = Color3.fromHex("161616"), 
					FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
					FontSize = Enum.FontSize.Size14, 
					Name = "picker", 
					Position = UDim2.new(0, 294, 0, 560), 
					Size = UDim2.new(0, 180, 0, 172), 
					Text = "", 
					TextColor3 = Color3.fromHex("000000"), 
					TextSize = 14, 
					Visible = false, 
					ZIndex = 2
				}, {
					library:Create("UIStroke", { 
						ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
						Color = Color3.fromHex("303030"), 
						Name = "stroke"
					}),
					library:Create("UICorner", { 
						CornerRadius = UDim.new(0, 6), 
						Name = "corner"
					}),
					library:Create("TextButton", { 
						AutoButtonColor = false, 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size14, 
						Name = "clickThroughBlock", 
						Size = UDim2.new(1, 0, 1, 0), 
						Text = "", 
						TextColor3 = Color3.fromHex("000000"), 
						TextSize = 14
					}),
					library:Create("ImageLabel", { 
						AnchorPoint = Vector2.new(0.5, 0.5), 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						Image = "rbxassetid://12725382410", 
						ImageColor3 = Color3.fromHex("0a0a0a"), 
						Name = "blur", 
						Position = UDim2.new(0.5, 0, 0.5, 0), 
						ScaleType = Enum.ScaleType.Slice, 
						Size = UDim2.new(1, 10, 1, 10), 
						SliceCenter = Rect.new(10, 10, 118, 118)
					}),
					library:Create("Frame", { 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						Name = "sat", 
						Position = UDim2.new(0, 5, 0, 5), 
						Size = UDim2.new(0, 140, 0, 100), 
						ZIndex = 2
					}, {
						library:Create("UICorner", { 
							CornerRadius = UDim.new(0, 3), 
							Name = "corner"
						}),
						library:Create("UIStroke", { 
							ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
							Color = Color3.fromHex("303030"), 
							Name = "stroke"
						}),
						library:Create("UIGradient", { 
							Color = ColorSequence.new({ 
								ColorSequenceKeypoint.new(0, Color3.fromHex("ffffff")), 
								ColorSequenceKeypoint.new(1, Color3.fromHex("00ff48"))
							}), 
							Name = "gradient"
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(0.5, 0.5), 
							BackgroundColor3 = Color3.fromHex("ffffff"), 
							Name = "val", 
							Position = UDim2.new(0.5, 0, 0.5, 0), 
							Size = UDim2.new(1, 0, 1, 0), 
							ZIndex = 2
						}, {
							library:Create("UICorner", { 
								CornerRadius = UDim.new(0, 3), 
								Name = "corner"
							}),
							library:Create("UIStroke", { 
								ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
								Color = Color3.fromHex("303030"), 
								Name = "stroke"
							}),
							library:Create("UIGradient", { 
								Color = ColorSequence.new({ 
									ColorSequenceKeypoint.new(0, Color3.fromHex("000000")), 
									ColorSequenceKeypoint.new(1, Color3.fromHex("000000"))
								}), 
								Name = "gradient", 
								Rotation = 270, 
								Transparency = NumberSequence.new({ 
									NumberSequenceKeypoint.new(0, 0), 
									NumberSequenceKeypoint.new(1, 1)
								})
							})
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(0.5, 0.5), 
							BackgroundColor3 = Color3.fromHex("45ff7a"), 
							Name = "indicator", 
							Position = UDim2.new(0.729, 0, 0, 0), 
							Size = UDim2.new(0, 12, 0, 12), 
							ZIndex = 3
						}, {
							library:Create("UIStroke", { 
								ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
								Color = Color3.fromHex("303030"), 
								Name = "stroke"
							}),
							library:Create("UICorner", { 
								CornerRadius = UDim.new(1, 0), 
								Name = "corner"
							})
						})
					}),
					library:Create("Frame", { 
						AnchorPoint = Vector2.new(1, 0), 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						Name = "hue", 
						Position = UDim2.new(1, -5, 0, 5), 
						Size = UDim2.new(0, 24, 0, 100), 
						ZIndex = 2
					}, {
						library:Create("UICorner", { 
							CornerRadius = UDim.new(0, 3), 
							Name = "corner"
						}),
						library:Create("UIStroke", { 
							ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
							Color = Color3.fromHex("303030"), 
							Name = "stroke"
						}),
						library:Create("UIGradient", { 
							Color = ColorSequence.new({ 
								ColorSequenceKeypoint.new(0, Color3.fromHex("ff0004")), 
								ColorSequenceKeypoint.new(1 / 6, Color3.fromHex("ffff00")), 
								ColorSequenceKeypoint.new(1 / 3, Color3.fromHex("00ff00")), 
								ColorSequenceKeypoint.new(0.5, Color3.fromHex("00ffff")), 
								ColorSequenceKeypoint.new(2 / 3, Color3.fromHex("0000ff")), 
								ColorSequenceKeypoint.new(5 / 6, Color3.fromHex("ff00ff")), 
								ColorSequenceKeypoint.new(1, Color3.fromHex("ff0004"))
							}), 
							Name = "gradient", 
							Rotation = 90
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(0.5, 0.5), 
							BackgroundColor3 = Color3.fromHex("00ff48"), 
							Name = "indicator", 
							Position = UDim2.new(0.5, 0, 0.379, 0), 
							Size = UDim2.new(1, 0, 0, 8), 
							ZIndex = 2
						}, {
							library:Create("UIStroke", { 
								ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
								Color = Color3.fromHex("303030"), 
								Name = "stroke"
							}),
							library:Create("UICorner", { 
								CornerRadius = UDim.new(1, 0), 
								Name = "corner"
							})
						})
					}),
					library:Create("TextBox", { 
						AnchorPoint = Vector2.new(0, 1), 
						BackgroundColor3 = Color3.fromHex("222222"), 
						FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size18, 
						Name = "hex", 
						PlaceholderColor3 = Color3.fromHex("b2b2b2"), 
						Position = UDim2.new(0, 5, 1, -37), 
						Size = UDim2.new(0.5, -8, 0, 24), 
						Text = "#45FF7A", 
						TextColor3 = Color3.fromHex("ebebeb"), 
						TextSize = 15, 
						ZIndex = 2
					}, {
						library:Create("UICorner", { 
							CornerRadius = UDim.new(0, 3), 
							Name = "corner"
						}),
						library:Create("UIStroke", { 
							ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
							Color = Color3.fromHex("303030"), 
							Name = "stroke"
						})
					}),
					library:Create("TextBox", { 
						AnchorPoint = Vector2.new(1, 1), 
						BackgroundColor3 = Color3.fromHex("222222"), 
						FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size18, 
						Name = "rgb", 
						PlaceholderColor3 = Color3.fromHex("b2b2b2"), 
						Position = UDim2.new(1, -5, 1, -37), 
						Size = UDim2.new(0.5, -8, 0, 24), 
						Text = "69, 255, 122", 
						TextColor3 = Color3.fromHex("ebebeb"), 
						TextSize = 15, 
						ZIndex = 2
					}, {
						library:Create("UICorner", { 
							CornerRadius = UDim.new(0, 3), 
							Name = "corner"
						}),
						library:Create("UIStroke", { 
							ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
							Color = Color3.fromHex("303030"), 
							Name = "stroke"
						})
					}),
					library:Create("TextButton", { 
						AnchorPoint = Vector2.new(0.5, 1), 
						AutoButtonColor = false, 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size14, 
						Name = "rainbow", 
						Position = UDim2.new(0.5, 0, 1, -2), 
						Size = UDim2.new(1, -4, 0, 32), 
						Text = "", 
						TextColor3 = Color3.fromHex("000000"), 
						TextSize = 14, 
						ZIndex = 2
					}, {
						library:Create("TextLabel", { 
							AnchorPoint = Vector2.new(0.5, 0), 
							BackgroundColor3 = Color3.fromHex("ffffff"), 
							BackgroundTransparency = 1, 
							FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
							FontSize = Enum.FontSize.Size18, 
							Name = "title", 
							Position = UDim2.new(0.5, 0, 0, 0), 
							Size = UDim2.new(1, -20, 0, 30), 
							Text = "Rainbow", 
							TextColor3 = Color3.fromHex("dcdcdc"), 
							TextSize = 17, 
							TextXAlignment = Enum.TextXAlignment.Left, 
							ZIndex = 2
						}),
						library:Create("Frame", { 
							AnchorPoint = Vector2.new(1, 0.5), 
							BackgroundColor3 = Color3.fromHex("1c1c1c"), 
							Name = "background", 
							Position = UDim2.new(1, -14, 0.5, 0), 
							Size = UDim2.new(0, 24, 0, 16), 
							ZIndex = 2
						}, {
							library:Create("UIStroke", { 
								ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
								Color = Color3.fromHex("303030"), 
								Name = "stroke"
							}),
							library:Create("UICorner", { 
								CornerRadius = UDim.new(1, 0), 
								Name = "corner"
							}),
							library:Create("Frame", { 
								AnchorPoint = Vector2.new(0.5, 0.5), 
								BackgroundColor3 = Color3.fromHex("45ff7a"), 
								Name = "indicator", 
								Position = UDim2.new(0.5, 10, 0.5, 0), 
								Size = UDim2.new(0, 20, 0, 20), 
								ZIndex = 2
							}, {
								library:Create("UICorner", { 
									CornerRadius = UDim.new(1, 0), 
									Name = "corner"
								}),
								library:Create("UIStroke", { 
									ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
									Color = Color3.fromHex("404040"), 
									Name = "stroke"
								})
							})
						})
					})
				}),
				library:Create("TextButton", { 
					AutoButtonColor = false, 
					BackgroundColor3 = Color3.fromHex("161616"), 
					FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
					FontSize = Enum.FontSize.Size14, 
					Name = "dropdown", 
					Position = UDim2.new(0, 100, 0, 560), 
					Size = UDim2.new(0, 200, 0, 142), 
					Text = "", 
					TextColor3 = Color3.fromHex("000000"), 
					TextSize = 14,
					Visible = false
				}, {
					library:Create("UIStroke", { 
						ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
						Color = Color3.fromHex("303030"), 
						Name = "stroke"
					}),
					library:Create("UICorner", { 
						CornerRadius = UDim.new(0, 6), 
						Name = "corner"
					}),
					library:Create("ScrollingFrame", { 
						Active = true, 
						AnchorPoint = Vector2.new(1, 0.5), 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						BorderSizePixel = 0, 
						BottomImage = "rbxassetid://12732022493", 
						CanvasSize = UDim2.new(0, 0, 0, 134), 
						MidImage = "rbxassetid://12732022370", 
						Name = "container", 
						Position = UDim2.new(1, 0, 0.5, 0), 
						ScrollBarImageColor3 = Color3.fromHex("222222"), 
						ScrollBarThickness = 4, 
						ScrollingDirection = Enum.ScrollingDirection.Y, 
						Size = UDim2.new(1, -4, 1, -8), 
						TopImage = "rbxassetid://12732022217", 
						VerticalScrollBarInset = Enum.ScrollBarInset.ScrollBar
					}, {
						library:Create("UIListLayout", { 
							Name = "list", 
							Padding = UDim.new(0, 1), 
							SortOrder = Enum.SortOrder.LayoutOrder
						})
					}),
					library:Create("TextButton", { 
						AutoButtonColor = false, 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size14, 
						Name = "clickThroughBlock", 
						Size = UDim2.new(1, 0, 1, 0), 
						Text = "", 
						TextColor3 = Color3.fromHex("000000"), 
						TextSize = 14, 
						ZIndex = 0
					}),
					library:Create("ImageLabel", { 
						AnchorPoint = Vector2.new(0.5, 0.5), 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						Image = "rbxassetid://12725382410", 
						ImageColor3 = Color3.fromHex("0a0a0a"), 
						Name = "blur", 
						Position = UDim2.new(0.5, 0, 0.5, 0), 
						ScaleType = Enum.ScaleType.Slice, 
						Size = UDim2.new(1, 10, 1, 10), 
						SliceCenter = Rect.new(10, 10, 118, 118), 
						ZIndex = 0
					})
				})
			}),
			library:Create("ScreenGui", {
				DisplayOrder = 12,
				Name = "Notifications",
				ResetOnSpawn = false
			}, {
				library:Create("Frame", {
					AnchorPoint = Vector2.new(1, 0.5),
					BackgroundTransparency = 1,
					Name = "panel",
					Position = UDim2.new(1, -15, 0.5, 0),
					Size = UDim2.new(0, 300, 1, -30)
				}, {
					library:Create("UIListLayout", {
						Name = "list",
						Padding = UDim.new(0, 10),
						SortOrder = Enum.SortOrder.LayoutOrder,
						VerticalAlignment = Enum.VerticalAlignment.Bottom
					})
				})
			}),
			library:Create("ScreenGui", {
				DisplayOrder = 10,
				Name = "Changelog",
				ResetOnSpawn = false
			}),
			library:Create("Folder", {
				Name = "DropIgnores"
			})
		});

		library.Store = library:Create("Folder", {
			Name = "storage",
			Parent = library.Directory
		});
		for i = 1, #library.Storage do
			library:Create("Folder", {
				Name = library.Storage[i],
				Parent = library.Store
			});
		end

		local main = library.Directory.UI.main;

		main.InputBegan:Connect(function(input)
			if (input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch) and library.Settings.Dragging == false then
				library.Settings.Dragging = true;
				local pos = Vector2.new(mouse.X - main.AbsolutePosition.X, mouse.Y - main.AbsolutePosition.Y);
				local mouseMove = mouse.Move:Connect(function()
					tween(main, library.Settings.DragLeniency, { Position = UDim2.new(0, mouse.X - pos.X, 0, mouse.Y - pos.Y) });
				end);
				local inputEnded; inputEnded = input.Changed:Connect(function()
					if input.UserInputState == Enum.UserInputState.End then
						mouseMove:Disconnect();
						inputEnded:Disconnect();
						library.Settings.Dragging = false;
					end
				end);
			end
		end);

		main.top.close.MouseButton1Click:Connect(function()
			library.Open = not library.Settings.Open;
		end);

		main.top.menu.MouseButton1Click:Connect(function()
			library.Menu = not library.Settings.Menu;
		end);

		main.left.discord.MouseButton1Click:Connect(function()
			setclipboard(library.Discord);
		end);

		local isTextBoxFocused = UserInputService:GetFocusedTextBox() ~= nil;

		UserInputService.TextBoxFocused:Connect(function()
			isTextBoxFocused = true;
		end);

		UserInputService.TextBoxFocusReleased:Connect(function()
			isTextBoxFocused = false;
		end);

		UserInputService.InputBegan:Connect(function(input)
			if library.Settings.Binding == false and not isTextBoxFocused then
				local enumItem = input.UserInputType == Enum.UserInputType.Keyboard and input.KeyCode or input.UserInputType;
				if enumItem.Name ~= "Escape" then
					for _, v in next, library.Items do
						if v.Class == "Bind" and v.Value.Key == enumItem and (v.Value.Dependency == nil or UserInputService:IsKeyDown(v.Value.Dependency)) then
							task.spawn(v.OnKeyDown);
						end
					end
				end
			end
		end);

		UserInputService.InputEnded:Connect(function(input)
			if library.Settings.Binding == false and not isTextBoxFocused then
				local enumItem = input.UserInputType == Enum.UserInputType.Keyboard and input.KeyCode or input.UserInputType;
				if enumItem.Name ~= "Escape" then
					for _, v in next, library.Items do
						if v.Class == "Bind" and v.Value.Key == enumItem and (v.Value.Dependency == nil or UserInputService:IsKeyDown(v.Value.Dependency)) then
							task.spawn(v.OnKeyUp);
						end
					end
				end
			end
		end);

		autoResize(library.Directory.Popups.dropdown.container.list, library.Directory.Popups.dropdown.container, 0);
		safeParent(library.Directory);

		return library;
	end

	function Library:Create(class, props, children)
		local inst = Instance.new(class);
		for i, v in next, props do
			if i ~= "Parent" then
				inst[i] = v;
			end
		end
		if children then
			for i = 1, #children do
				children[i].Parent = inst;
			end
		end
		inst.Parent = props.Parent;
		return inst;
	end

	function Library:AddTab(options)
		return Tab.new(self, options);
	end

	function Library:Notify(options)
		local notification = mergeTables({
			Title = "Notification",
			Message = "Undefined Notification Message",
			Duration = 5,
			Buttons = { "Dismiss" },
			Callback = function() end
		}, options);
		
		local frame = self:Create("Frame", { 
			BackgroundTransparency = 1,
			Name = notification.Title, 
			Parent = self.Directory.Notifications.panel, 
			Size = UDim2.new(1, 0, 0, TextService:GetTextBoundsAsync(self:Create("GetTextBoundsParams", {
				Text = notification.Message,
				Font = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal),
				Size = 13,
				Width = 274
			})).Y + 55)
		}, {
			self:Create("Frame", { 
				AnchorPoint = Vector2.new(0.5, 0.5), 
				BackgroundColor3 = Color3.fromHex("161616"), 
				Name = "container", 
				Position = UDim2.new(2, 0, 0.5, 0), 
				Size = UDim2.new(1, 0, 1, 0)
			}, {
				self:Create("UICorner", { 
					CornerRadius = UDim.new(0, 3), 
					Name = "corner"
				}),
				self:Create("Frame", { 
					AnchorPoint = Vector2.new(1, 1), 
					BackgroundColor3 = Color3.fromHex("ffffff"), 
					BackgroundTransparency = 1, 
					BorderSizePixel = 0, 
					Name = "container", 
					Position = UDim2.new(1, -10, 1, -10), 
					Size = UDim2.new(1, -20, 0, 22)
				}, {
					self:Create("UIListLayout", { 
						FillDirection = Enum.FillDirection.Horizontal, 
						HorizontalAlignment = Enum.HorizontalAlignment.Right, 
						Name = "list", 
						Padding = UDim.new(0, 6), 
						SortOrder = Enum.SortOrder.LayoutOrder
					})
				}),
				self:Create("Frame", { 
					AnchorPoint = Vector2.new(0, 1), 
					BackgroundColor3 = Color3.fromHex("45ff7a"), 
					Name = "timeout", 
					Position = UDim2.new(0, 0, 1, 0), 
					Size = UDim2.new(0, 0, 0, 6)
				}, {
					self:Create("UICorner", { 
						CornerRadius = UDim.new(0, 3), 
						Name = "corner"
					}),
					self:Create("Frame", { 
						AnchorPoint = Vector2.new(0.5, 0), 
						BackgroundColor3 = Color3.fromHex("161616"), 
						BorderSizePixel = 0, 
						Name = "cover", 
						Position = UDim2.new(0.5, 0, 0, 0), 
						Size = UDim2.new(1, 0, 0.5, 0)
					})
				}),
				self:Create("ImageLabel", { 
					AnchorPoint = Vector2.new(0.5, 0.5), 
					BackgroundColor3 = Color3.fromHex("ffffff"), 
					BackgroundTransparency = 1, 
					Image = "rbxassetid://10189254800", 
					ImageColor3 = Color3.fromHex("0e0f13"), 
					Name = "blur", 
					Position = UDim2.new(0.5, 0, 0.5, 0), 
					ScaleType = Enum.ScaleType.Slice, 
					Size = UDim2.new(1, 8, 1, 8), 
					SliceCenter = Rect.new(10, 10, 118, 118), 
					ZIndex = 0
				}),
				self:Create("TextLabel", { 
					AnchorPoint = Vector2.new(0.5, 0), 
					BackgroundColor3 = Color3.fromHex("ffffff"), 
					BackgroundTransparency = 1, 
					FontFace = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
					FontSize = Enum.FontSize.Size14, 
					Name = "desc", 
					Position = UDim2.new(0.5, 0, 0, 13), 
					Size = UDim2.new(1, -26, 0, 13), 
					Text = notification.Message, 
					TextColor3 = Color3.fromHex("ffffff"), 
					TextSize = 13, 
					TextWrap = true, 
					TextWrapped = true, 
					TextXAlignment = Enum.TextXAlignment.Left
				})
			})
		});
		
		tween(frame.container, 0.5, { Position = UDim2.new(0.5, 0, 0.5, 0) }, Enum.EasingStyle.Quart);

		local function dismiss(argument)
			if frame.Parent ~= nil then
				tween(frame.container, 1, { Position = UDim2.new(2, 0, 0.5, 0) }, Enum.EasingStyle.Quart).Completed:Connect(function()
					frame:Destroy();
				end);
				notification.Callback(argument);
			end
		end
		
		for i = 1, #notification.Buttons do
			local buttonName = notification.Buttons[i];
			local name = tostring(buttonName);
			
			local font = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Medium, Enum.FontStyle.Normal);
			
			local button = self:Create("TextButton", {
				Parent = frame.container.container,
				FontFace = font,
				FontSize = Enum.FontSize.Size14,
				Text = name,
				TextColor3 = Color3.fromHex("ebebeb"),
				TextSize = 13,
				AutoButtonColor = false,
				BackgroundTransparency = 1,
				Size = UDim2.new(0, TextService:GetTextBoundsAsync(self:Create("GetTextBoundsParams", {
					Text = name,
					Font = font,
					Size = 13,
					Width = math.huge
				})).X + 10, 1, 0),
				Name = name
			}, {
				self:Create("UICorner", {
					CornerRadius = UDim.new(0, 3),
					Name = "corner"
				})
			});

			button.MouseButton1Click:Connect(function()
				dismiss(name);
			end);
		end

		tween(frame.container.timeout, notification.Duration, { Size = UDim2.new(1, 0, 0, 6) }, Enum.EasingStyle.Linear).Completed:Connect(function()
			dismiss("Timeout");
		end);
	end

	function Library:Changelog(ver, invite, log)
		local changelog = self:Create("Frame", { 
			AnchorPoint = Vector2.new(0.5, 0.5), 
			BackgroundColor3 = Color3.fromHex("161616"), 
			Name = "main", 
			Parent = self.Directory.Changelog, 
			Position = UDim2.new(0.5, 0, 0.5, 0), 
			Size = UDim2.new(0, 300, 0, 350)
		}, {
			self:Create("TextButton", { 
				AutoButtonColor = false, 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
				FontSize = Enum.FontSize.Size14, 
				Name = "clickThroughBlock", 
				Size = UDim2.new(1, 0, 1, 0), 
				Text = "", 
				TextColor3 = Color3.fromHex("000000"), 
				TextSize = 14, 
				ZIndex = 0
			}),
			self:Create("ImageLabel", { 
				AnchorPoint = Vector2.new(0.5, 0.5), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Image = "rbxassetid://12725382410", 
				ImageColor3 = Color3.fromHex("0a0a0a"), 
				Name = "blur", 
				Position = UDim2.new(0.5, 0, 0.5, 0), 
				ScaleType = Enum.ScaleType.Slice, 
				Size = UDim2.new(1, 10, 1, 10), 
				SliceCenter = Rect.new(10, 10, 118, 118), 
				ZIndex = 0
			}),
			self:Create("UICorner", { 
				CornerRadius = UDim.new(0, 6), 
				Name = "corner"
			}),
			self:Create("Frame", { 
				AnchorPoint = Vector2.new(1, 1), 
				BackgroundColor3 = Color3.fromHex("ffffff"), 
				BackgroundTransparency = 1, 
				Name = "bottom", 
				Position = UDim2.new(1, 0, 1, 0), 
				Size = UDim2.new(1, 0, 0, 28)
			}, {
				self:Create("TextLabel", { 
					AnchorPoint = Vector2.new(0.5, 0.5), 
					BackgroundColor3 = Color3.fromHex("ffffff"), 
					BackgroundTransparency = 1, 
					FontFace = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
					FontSize = Enum.FontSize.Size14, 
					Name = "version", 
					Position = UDim2.new(0.5, 0, 0.5, 0), 
					Size = UDim2.new(1, -16, 1, 0), 
					Text = ver, 
					TextColor3 = Color3.fromHex("ffffff"), 
					TextSize = 13, 
					TextXAlignment = Enum.TextXAlignment.Right
				}),
				self:Create("TextLabel", { 
					AnchorPoint = Vector2.new(0.5, 0.5), 
					BackgroundColor3 = Color3.fromHex("ffffff"), 
					BackgroundTransparency = 1, 
					FontFace = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
					FontSize = Enum.FontSize.Size14, 
					Name = "discord", 
					Position = UDim2.new(0.5, 0, 0.5, 0), 
					Size = UDim2.new(1, -16, 1, 0), 
					Text = invite, 
					TextColor3 = Color3.fromHex("ffffff"), 
					TextSize = 13, 
					TextXAlignment = Enum.TextXAlignment.Left
				})
			}),
			self:Create("Frame", { 
				AnchorPoint = Vector2.new(0.5, 0), 
				BackgroundColor3 = Color3.fromHex("1c1c1c"), 
				Name = "container", 
				Position = UDim2.new(0.5, 0, 0, 9), 
				Size = UDim2.new(1, -18, 1, -47), 
				ZIndex = 2
			}, {
				self:Create("UICorner", { 
					CornerRadius = UDim.new(0, 3), 
					Name = "corner"
				}),
				self:Create("ImageLabel", { 
					AnchorPoint = Vector2.new(0.5, 0.5), 
					BackgroundColor3 = Color3.fromHex("ffffff"), 
					BackgroundTransparency = 1, 
					Image = "rbxassetid://10189254800", 
					ImageColor3 = Color3.fromHex("000105"), 
					Name = "blur", 
					Position = UDim2.new(0.5, 0, 0.5, 0), 
					ScaleType = Enum.ScaleType.Slice, 
					Size = UDim2.new(1, 10, 1, 10), 
					SliceCenter = Rect.new(10, 10, 118, 118)
				}),
				self:Create("UIStroke", { 
					ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
					Color = Color3.fromHex("323337"), 
					Name = "stroke"
				}),
				self:Create("Frame", { 
					AnchorPoint = Vector2.new(0.5, 0), 
					BackgroundColor3 = Color3.fromHex("ffffff"), 
					BackgroundTransparency = 1, 
					Name = "user", 
					Position = UDim2.new(0.5, 0, 0, 5), 
					Size = UDim2.new(1, -10, 0, 74), 
					ZIndex = 2
				}, {
					self:Create("ImageLabel", { 
						AnchorPoint = Vector2.new(1, 0.5), 
						BackgroundColor3 = Color3.fromHex("161616"), 
						Image = Players:GetUserThumbnailAsync(LocalPlayer.UserId, Enum.ThumbnailType.HeadShot, Enum.ThumbnailSize.Size150x150), 
						Name = "icon", 
						Position = UDim2.new(1, -5, 0.5, 0), 
						Size = UDim2.new(0, 64, 0, 64), 
						ZIndex = 2
					}, {
						self:Create("UICorner", { 
							CornerRadius = UDim.new(1, 0), 
							Name = "corner"
						}),
						self:Create("UIStroke", { 
							ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
							Color = Color3.fromHex("323337"), 
							Name = "stroke"
						})
					}),
					self:Create("TextLabel", { 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						FontFace = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Medium, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size18, 
						Name = "welcome", 
						Position = UDim2.new(0, 14, 0, 37), 
						Size = UDim2.new(1, -14, 0, 26), 
						Text = "Welcome, \n" .. LocalPlayer.Name, 
						TextColor3 = Color3.fromHex("ffffff"), 
						TextSize = 16, 
						TextXAlignment = Enum.TextXAlignment.Left, 
						TextYAlignment = Enum.TextYAlignment.Bottom, 
						ZIndex = 2
					}),
					self:Create("TextLabel", { 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						FontFace = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Medium, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size24, 
						Name = "title", 
						Position = UDim2.new(0, 14, 0, 4), 
						Size = UDim2.new(1, -14, 0, 26), 
						Text = "Jailbreaker", 
						TextColor3 = Color3.fromHex("45ff7a"), 
						TextSize = 20, 
						TextXAlignment = Enum.TextXAlignment.Left, 
						TextYAlignment = Enum.TextYAlignment.Bottom, 
						ZIndex = 2
					})
				}),
				self:Create("Frame", { 
					AnchorPoint = Vector2.new(0.5, 0), 
					BackgroundColor3 = Color3.fromHex("161616"), 
					Name = "updates", 
					Position = UDim2.new(0.5, 0, 0, 84), 
					Size = UDim2.new(1, -18, 1, -126), 
					ZIndex = 2
				}, {
					self:Create("UIStroke", { 
						ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
						Color = Color3.fromHex("323337"), 
						Name = "stroke"
					}),
					self:Create("UICorner", { 
						CornerRadius = UDim.new(0, 3), 
						Name = "corner"
					}),
					self:Create("ScrollingFrame", { 
						Active = true, 
						AnchorPoint = Vector2.new(1, 1), 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						BorderSizePixel = 0, 
						BottomImage = "rbxassetid://10189246540", 
						MidImage = "rbxassetid://10189246358", 
						Name = "container", 
						Position = UDim2.new(1, -4, 1, -4), 
						ScrollBarImageColor3 = Color3.fromHex("323337"), 
						ScrollBarThickness = 4, 
						Size = UDim2.new(1, -12, 1, -40), 
						TopImage = "rbxassetid://10189246196", 
						ZIndex = 2
					}, {
						self:Create("TextLabel", { 
							BackgroundColor3 = Color3.fromHex("ffffff"), 
							BackgroundTransparency = 1, 
							FontFace = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
							FontSize = Enum.FontSize.Size14, 
							Name = "changelog", 
							Size = UDim2.new(1, 0, 1, 0), 
							Text = "",
							TextColor3 = Color3.fromHex("ffffff"), 
							TextSize = 13, 
							TextWrap = true, 
							TextWrapped = true, 
							TextXAlignment = Enum.TextXAlignment.Left, 
							TextYAlignment = Enum.TextYAlignment.Top, 
							ZIndex = 2
						})
					}),
					self:Create("Frame", { 
						AnchorPoint = Vector2.new(0.5, 0), 
						BackgroundColor3 = Color3.fromHex("323337"), 
						BorderSizePixel = 0, 
						Name = "separator", 
						Position = UDim2.new(0.5, 0, 0, 28), 
						Size = UDim2.new(1, 0, 0, 1), 
						ZIndex = 2
					}),
					self:Create("TextLabel", { 
						AnchorPoint = Vector2.new(0.5, 0), 
						BackgroundColor3 = Color3.fromHex("ffffff"), 
						BackgroundTransparency = 1, 
						FontFace = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
						FontSize = Enum.FontSize.Size14, 
						Name = "title", 
						Position = UDim2.new(0.5, 0, 0, 2), 
						Size = UDim2.new(1, -16, 0, 24), 
						Text = "Update Log", 
						TextColor3 = Color3.fromHex("ffffff"), 
						TextSize = 13, 
						ZIndex = 2
					})
				}),
				self:Create("TextButton", { 
					AnchorPoint = Vector2.new(0.5, 1), 
					AutoButtonColor = false, 
					BackgroundColor3 = Color3.fromHex("161616"), 
					FontFace = Font.new("rbxasset://fonts/families/GothamSSm.json", Enum.FontWeight.Regular, Enum.FontStyle.Normal), 
					FontSize = Enum.FontSize.Size14, 
					Name = "launch", 
					Position = UDim2.new(0.5, 0, 1, -9), 
					Size = UDim2.new(1, -18, 0, 24), 
					Text = "Launch", 
					TextColor3 = Color3.fromHex("ffffff"), 
					TextSize = 13, 
					ZIndex = 2
				}, {
					self:Create("UICorner", { 
						CornerRadius = UDim.new(0, 3), 
						Name = "corner"
					}),
					self:Create("UIStroke", { 
						ApplyStrokeMode = Enum.ApplyStrokeMode.Border, 
						Color = Color3.fromHex("323337"), 
						Name = "stroke"
					})
				})
			}),
			self:Create("Frame", { 
				AnchorPoint = Vector2.new(0.5, 1), 
				BackgroundColor3 = Color3.fromHex("323337"), 
				BorderSizePixel = 0, 
				Name = "separator", 
				Position = UDim2.new(0.5, 0, 1, -28), 
				Size = UDim2.new(1, 0, 0, 1)
			})
		});
		
		local updateContainer, str = changelog.container.updates.container, "";
		for i = 1, #log do
			local v = log[i];
			str = string.format("%s%s%s\n%s", str, str == "" and "" or "\n", v.timestamp, v.message);
		end
		updateContainer.changelog.Text = str;
		updateContainer.CanvasSize = UDim2.new(0, TextService:GetTextBoundsAsync(self:Create("GetTextBoundsParams", {
			Text = updateContainer.changelog.Text,
			Font = updateContainer.changelog.FontFace,
			Size = updateContainer.changelog.TextSize,
			Width = updateContainer.changelog.AbsoluteSize.X
		})).Y, 0, 0);
		
		changelog.container.launch.MouseButton1Click:Connect(function()
			self.Directory.Changelog.Enabled = false;
			self.Open = true;
		end);
		
		self.Directory.Changelog.Enabled = true;
	end
end

if JB_DEBUG then
	warn("[Jailbreaker Debugging]: Setting Up User Interfaces..")
end

--// Main UI

local Frame = Library.new({ Title = "Jailbreaker "..JailbreakerVersion });

--// Tabs

local Home        = Frame:AddTab({ Title = "Home", Icon = "rbxassetid://13256509240" }):Select();
local SettingsTab = Frame:AddTab({ Title = "Settings", Icon = "rbxassetid://13256505795" })
local RobberyTab  = Frame:AddTab({ Title = "Robberies", Icon = "rbxassetid://13312339459" })
local Teleports   = Frame:AddTab({ Title = "Teleports", Icon = "rbxassetid://13256501848" })
local Misc        = Frame:AddTab({ Title = "Other", Icon = "rbxassetid://13256525870" })

--// Home Tab

local Information = Home:AddSection({ Title = "Information"});
local Credits     = Home:AddSection({ Title = "Credits" });
local Autorob     = Home:AddSection({
	Title = "Auto Rob",
	Side = LibraryEnum.SectionSide.Right
})

do
	if JB_DEBUG then
		warn("[Jailbreaker Debugging] [Home Tab]: Fetching Infomations..")
	end

	local Executions = ExecutionCount or "Unknown"
	local DiscordId  = DiscordID or "Unknown"
	local MainURL = "https://jailbreakerv2utils.brizzy9999.repl.co/"

	Information:AddLabel({ Title = "Discord ID: ".. DiscordId ..".", Flag = "ExampleLabel" });
	Information:AddLabel({ Title = "Key Executions: ".. Executions ..".", Flag = "ExampleLabel" });

	spawn(function()
		local DiscordMembers = game:HttpGet(MainURL.."/api/discord/members")
		local DiscordInvite  = game:HttpGet(MainURL.."/api/discord/invite")

		local CreditsKieran  = game:HttpGet(MainURL.."/api/credits/kieran")
		local CreditsFayy    = game:HttpGet(MainURL.."/api/credits/fayy")
		local CreditsBrizzy  = game:HttpGet(MainURL.."/api/credits/brizzy")
		local CreditsMin     = game:HttpGet(MainURL.."/api/credits/min")

		Information:AddLabel({ Title = "Total discord members: ".. DiscordMembers, Flag = "ExampleLabel" });
		Information:AddLabel({ Title = "Discord Invite: ".. DiscordInvite, Flag = "ExampleLabel" });

		Credits:AddLabel({ Title = CreditsMin.." - Scripter", Flag = "ExampleLabel" });
		Credits:AddLabel({ Title = CreditsBrizzy.." - Scripter", Flag = "ExampleLabel" });
		Credits:AddLabel({ Title = CreditsKieran.." - UI Creator", Flag = "ExampleLabel" });
		Credits:AddLabel({ Title = CreditsFayy.." - Helping with Bank and CargoShip", Flag = "ExampleLabel" });
	end)


	if JB_DEBUG then
		warn("[Jailbreaker Debugging] [Home Tab]: Loading Sections & Buttons & Toggles & Text..")
	end

	Autorob:AddToggle({
		Title = "Toggled",
		Flag = "ExampleToggle",
		Value = (getgenv().V2_ServerHop or false),
		Callback = function(state)
			spawn(ToggleAutoRob, state)
		end
	});
	Autorob:AddToggle({
		Title = "Auto Switch Server",
		Value = (Settings.AutoSwitchServer or false),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.AutoSwitchServer = state
		end
	});
	Autorob:AddToggle({
		Title = "Auto Open Safe",
		Value = (Settings.AutoOpenSafe or false),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.AutoOpenSafe = state
		end
	});
	Autorob:AddToggle({
		Title = "Hide UI On New Server",
		Value = (Settings.HideUIOnNewServer or false),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.HideUIOnNewServer = state
		end
	});
	Autorob:AddToggle({
		Title = "Small Server",
		Value = (Settings.SmallServer or false),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.SmallServer = state
		end
	});

	local status = Autorob:AddStatus({ Title = "Status:", Flag = "ExampleStatus", Status = "Loading.." });

	--local CurrentStatus = "Loading.."
	
	do
		local Fetching = false

		function SetStatus(Status)
			-- PreviousStatus           = CurrentStatus
			-- CurrentStatus            = Status
			status.Frame.status.Text = Status

			if AutoRobbing and Settings.WebhookEnabled and Settings.WebhookUrl then
				spawn(Request, {
					Url = Settings.WebhookUrl,
					Method = "POST",
					Headers = {
						["Content-Type"] = "application/json"
					},
					Body = HttpService:JSONEncode(
						{
							username = "Jailbreaker V2",
							embeds = {
								{
									--color = Settings.WebhookColor,
									title = "Jailbreaker V2",
									fields = {
										{
											name = "`💰` Status: "..Status,
											value = "```ini\n[Time Elapsed]: "..GetTimeElapsed().."\n[Current Money]: $".. tostring(math.floor(LocalPlayer.leaderstats.Money.Value)):reverse():gsub("(%d%d%d)", "%1,"):gsub(",(%-?)$", "%1"):reverse() .."\n[Money Earned]: $"..tostring(GetCashEarned()):reverse():gsub("(%d%d%d)", "%1,"):gsub(",(%-?)$", "%1"):reverse().."\n[Estimated Hour Earning]: $".. tostring(GetEstimated()):reverse():gsub("(%d%d%d)", "%1,"):gsub(",(%-?)$", "%1"):reverse() .."```",
											inline = true
										},
									},
									timestamp = DateTime.now():ToIsoDate(),
									footer = {
										text = "https://jailbreaker.site/"
									}
								}
							}
						}
					)
				})
			end
		end
	end
	
	local TimeLab 		= Autorob:AddStatus({ Title = "Time Elapsed:", Flag = "ExampleStatus", Status = "Loading.." });
	local EarnedLab 	= Autorob:AddStatus({ Title = "Money Earned:", Flag = "ExampleStatus", Status = "Loading.." });
	local EstLab 		= Autorob:AddStatus({ Title = "Estimated Hour Earning:", Flag = "ExampleStatus", Status = "Loading.." });
	local LastEarned = 1
	
	do
		function SetEarned(Earned)
			if Earned ~= LastEarned then
				EarnedLab.Frame.status.Text = Earned
			end
		end
		function SetTime(Time)
			TimeLab.Frame.status.Text = Time
		end
		function SetEstimated(Amount)
			EstLab.Frame.status.Text = Amount
		end
	
		SetEarned("$0")
		SetEstimated("$0")
		SetTime("00d:00h:00m:00s")
	end
end

if JB_DEBUG then
	warn("[Jailbreaker Debugging] [Settings Tab]: Loading Sections & Buttons & Toggles & Text..")
end

--// Settings Tab

local TeleportSettings = SettingsTab:AddSection({Title = "Teleportation"})
local KillAuraSection  = SettingsTab:AddSection({Title = "Kill Aura"})
local RobberySettings = SettingsTab:AddSection({ Title = "Other" , Side = LibraryEnum.SectionSide.Right });

do
    local Notified = false
	local TeleportMethods = TeleportSettings:AddDropdown({
		Title = "Teleport Methods",
		Flag = "ExampleDrop",
		Items = {
			"V2 (Jailbreaker V2)",
			"V1 (Jailbreaker V1)",
			"Tween"
		},
		AllowNoValue = true,
		MultiSelect = false,
		Callback = function(value, state)
			Settings.TeleportMethod = value:match("%S+")
		end
	})

	for i, Method in pairs({"V2 (Jailbreaker V2)", "V1 (Jailbreaker V1)", "Tween"}) do
		if Settings.TeleportMethod == Method:match("%S+") then
			TeleportMethods:Set(Method, true)
			break
		end
	end

	TeleportSettings:AddSlider({
		Title = "Vehicle Teleport Speed",
		Value = (Settings.VehicleTpSpeed and (Settings.VehicleTpSpeed - 200) / (600 - 200) * 100 or 50),
		Min = 0, Max = 100,
		Flag = "ExampleSlider",
		Float = 1,
		ShowValue = true,
		StartName = "Slow",
		EndName = "Fast",
		Suffix = "%", Callback = function(value)
			Settings.VehicleTpSpeed = 200 + ((600 - 200) * (value / 100))
			if value > 75 and not Notified then
				Notification_new({
                    Text = "High speed may triggers the game anti-cheat and lag your character. We recommend speed below 75%.",
					Duration = 10,
				})
                Notified = true
			end
		end
	})
	TeleportSettings:AddSlider({
		Title = "Player Teleport Speed",
		Value = (Settings.PlayerTpSpeed and (Settings.PlayerTpSpeed - 16) / (150 - 16) * 100 or 50),
		Min = 0,
		Max = 100,
		Flag = "ExampleSlider",
		Float = 1,
		ShowValue = true,
		StartName = "Slow",
		EndName = "Fast",
		Suffix = "%",
		Callback = function(value)
			Settings.PlayerTpSpeed = 16 + ((150 - 16) * (value / 100))
			if value > 75 and not Notified then
				Notification_new({
					Text = "High speed may triggers the game anti-cheat and lag your character. We recommend using speed below 75%.",
					Duration = 10
				})
                Notified = true
			end
		end
	})
	TeleportSettings:AddSlider({
		Title = "Ground Teleport Speed",
		Value = (Settings.GroundTpSpeed and (Settings.GroundTpSpeed - 16) / (70 - 16) * 100 or 50),
		Min = 0,
		Max = 100,
		Flag = "ExampleSlider",
		Float = 1,
		ShowValue = true,
		StartName = "Slow",
		EndName = "Fast",
		Suffix = "%",
		Callback = function(value)
			Settings.GroundTpSpeed = 16 + ((70 - 16) * (value / 100))
			if value > 75 and not Notified then
				Notification_new({
					Text = "High speed nay triggers the game anti-cheat and lag your character. We recommend using speed below 75%.",
					Duration = 10
				})
                Notified = true
			end
		end
	})
	KillAuraSection:AddToggle({
		Title = "Toggled",
		Value = (Settings.KillAura or false),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.KillAura = state
		end
	})
	KillAuraSection:AddSlider({
		Title = "Range",
		Value = (Settings.KillAuraRange or 100),
		Min = 100,
		Max = 1000,
		Flag = "ExampleSlider",
		Float = 1,
		ShowValue = true,
		StartName = "Nearest",
		EndName = "Farthest",
		Callback = function(value)
			Settings.KillAuraRange = value
		end
	})
	KillAuraSection:AddDropdown({
		Title = "Kill Aura Gun",
		Flag = "ExampleDrop",
		Items = Guns,
		AllowNoValue = false,
		MultiSelect = false,
		Callback = function(value, state)
			SetKillAuraGun(value)
		end
	})

	local PlayerNames = {}

	for i, v in pairs(Players:GetPlayers()) do
		table.insert(PlayerNames, v.Name)
	end

	local KillAuraExcludeDrop = KillAuraSection:AddDropdown({
		Title = "Kill Aura Exclude",
		Flag = "ExampleDrop",
		Items = PlayerNames,
		AllowNoValue = true,
		MultiSelect = true,
		Callback = function(value, state)
			if state and not table.find(Settings.KillAuraExclude, value) then
				table.insert(Settings.KillAuraExclude, value)
			elseif not state and table.find(Settings.KillAuraExclude, value) then
				table.remove(Settings.KillAuraExclude, table.find(Settings.KillAuraExclude, value))
			end
		end
	})

	do
		for i, PlayerName in pairs(PlayerNames) do
			if table.find(Settings.KillAuraExclude, PlayerName) then
				KillAuraExcludeDrop:Set(PlayerName, true)
			end
		end
		Players.PlayerAdded:Connect(function(Player)
			KillAuraExcludeDrop:Add(Player.Name)
		end)
		Players.PlayerRemoving:Connect(function(Player)
			KillAuraExcludeDrop:Remove(Player.Name)
		end)
		KillAuraExcludeDrop:Remove(LocalPlayer.Name)
	end

	
	local UIFrameMain = Frame.Directory.UI
	RobberySettings:AddBind({
		Title = "UI Toggle",
		Value = {Key = Settings.UIToggle and Enum.KeyCode[Settings.UIToggle]},
		Flag = "ExampleBind",
		OnKeyDown = function()
			UIFrameMain.Enabled = not UIFrameMain.Enabled;
		end, OnKeyChanged = function(_, input)
			Settings.UIToggle = input.Key.Name
		end
	});
	RobberySettings:AddToggle({
		Title = "Serverhop On Auto Arrester",
		Value = (Settings.ServerhopOnAutoArrest or true),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.ServerhopOnAutoArrest = state
		end
	});
	RobberySettings:AddToggle({
		Title = "Instant Robbery Teleport",
		Value = (Settings.InstantRobberyTp or false),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.InstantRobberyTp = state
			for k, v in next, Robbery do
				v.InstantTp = state
			end
		end
	});
	RobberySettings:AddToggle({
		Title = "Bank Escape On Police Entered",
		Value = (Settings.BankEscapePoliceEntered or true),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.BankEscapePoliceEntered = state
		end
	});
	RobberySettings:AddToggle({
		Title = "Auto Pull Museum Lever",
		Value = (Settings.AutoPullMuseumLever or false),
		Callback = function(state)
			Settings.AutoPullMuseumLever = state
		end
	})
	RobberySettings:AddToggle({
		Title = "Auto Call Plane",
		Value = (Settings.AutoCallPlane or false),
		Callback = function(state)
			Settings.AutoCallPlane = state
		end
	})
	RobberySettings:AddToggle({
		Title = "Auto Lock Vehicle",
		Value = (Settings.LockCar or true),
		Flag = "ExampleToggle",
		Callback = function(state)
			Settings.LockCar = state
		end
	})
	RobberySettings:AddToggle({
		Title = "Anti Arrest (Will Auto Disable When Cargo Train)",
		Value = (Settings.AntiArrest or false),
		Callback = function(state)
			Settings.AntiArrest = state
		end
	})
	-- RobberySettings:AddToggle({
	-- 	Title = "Anti Arrest Say Message When Police Nearby",
	-- 	Value = (Settings.AntiArrestSayMessageWhenPoliceNearby or false),
	-- 	Callback = function(state)
	-- 		Settings.AntiArrestSayMessageWhenPoliceNearby = state
	-- 	end
	-- })
	-- RobberySettings:AddBox({
	-- 	Title = "Anti Arrest Say Message",
	-- 	Value = (Settings.AntiArrestSayMessage or "I am immuned by Jailbreaker Anti Arrest. Therefore you cannot arrest me."),
	-- 	Callback = function(value)
	-- 		Settings.AntiArrestSayMessage = value
	-- 	end
	-- })
	RobberySettings:AddSlider({
		Title = "PowerPlant Sell Value",
		Value = (Settings.PowerPlantUraniumValue or 5500),
		Min = 2500,
		Max = 6000,
		Flag = "ExampleSlider",
		Float = 50,
		ShowValue = true,
		StartName = "Empty",
		EndName = "Full",
		Callback = function(value)
			Settings.PowerPlantUraniumValue = value
		end
	});
    --[[
	RobberySettings:AddSlider({
		Title = "PowerPlant Numberlink Solve Wait",
		Value = (Settings.PowerPlantNumberlinkWait or 1),
		Min = 0,
		Max = 50,
		Flag = "ExampleSlider",
		Float = 1,
		ShowValue = true,
		StartName = "Empty",
		EndName = "Full",
		Callback = function(value)
			Settings.PowerPlantNumberlinkWait = value
		end
	});
    ]]
	RobberySettings:AddSlider({
		Title = "Robbery Bag Sell Value",
		Value = (Settings.BagSellValue or 10000),
		Min = 50,
		Max = 10000,
		Flag = "ExampleSlider",
		Float = 50,
		ShowValue = true,
		StartName = "Empty",
		EndName = "Full",
		Callback = function(value)
			Settings.BagSellValue = value
		end
	});
	RobberySettings:AddSlider({
		Title = "Museum Sell Wait",
		Value = (Settings.MuseumSellWait or 20),
		Min = 0,
		Max = 40,
		Flag = "ExampleSlider",
		Float = 1,
		ShowValue = true,
		StartName = "Empty",
		EndName = "Full",
		Callback = function(value)
			Settings.MuseumSellWait = value
		end
	});
	RobberySettings:AddSlider({
		Title = "Cargo Plane Sell Wait",
		Value = (Settings.PlaneWaitBeforeSell or 5),
		Min = 0,
		Max = 40,
		Flag = "ExampleSlider",
		Float = 1,
		ShowValue = true,
		StartName = "Empty",
		EndName = "Full",
		Callback = function(value)
			Settings.PlaneWaitBeforeSell = value
		end
	});
	RobberySettings:AddSlider({
		Title = "Robbery Cooldown",
		Value = (Settings.Cooldown or 0),
		Min = 0, Max = 60,
		Flag = "ExampleSlider",
		Float = 1,
		ShowValue = true,
		StartName = "Empty",
		EndName = "Full", Callback = function(value)
			Settings.Cooldown = value
		end
	});
end

if JB_DEBUG then
	warn("[Jailbreaker Debugging] [Robberies Tab]: Loading Sections & Toggles & Text..")
end

--// Robberies Tab

local RobberyStatesSect = RobberyTab:AddSection({ Title = "Robberies Status" , Side = LibraryEnum.SectionSide.Right });
local RobberyToggles    = RobberyTab:AddSection({ Title = "Robberies Toggles"  });

do
	for i, v in next, Robbery do
		local e = RobberyStatesSect:AddStatus({ Title = i..":", Flag = "ExampleStatus", Status = "Waiting" });

		local function UpdateStatus()
			if (i ~= "Airdrop" and v.Open) or (i == "Airdrop" and GetNearestAirdrop()) then
				e.Frame.status.TextColor3 = Color3.fromHex("45ff7a")
				e.Frame.status.Text = "Opened."
			else
				e.Frame.status.TextColor3 = Color3.fromHex("ff1100")
				e.Frame.status.Text = "Closed."
			end

			if LPH_OBFUSCATED then
				oldSetMt(whitelisted, nil)
				if #instCheck ~= 27 or not whitelisted[resp.Body] or not ExecutionCount or not DiscordID then
					while true do end;
					(nil)()
					return
				end
			end
		end

		UpdateStatus()
		Robbery.OnOpen:Connect(UpdateStatus)
	end

	for k, v in next, Robbery do
		RobberyToggles:AddToggle({ Title = k, Flag = "ExampleToggle", Value = v.Enabled, Callback = function(state)
			v.Enabled = state
			Settings.RobberyTogglesOff[k] = not state
		end});
	end
end

if JB_DEBUG then
	warn("[Jailbreaker Debugging] [Teleportation Tab]: Loading Sections & Buttons & Toggles & Text..")
end

--// Teleportation Tab

local RobberyTeleports = Teleports:AddSection({ Title = "Robberies Locations" });
local MiscTeleports = Teleports:AddSection({ Title = "Other Locations" , Side = LibraryEnum.SectionSide.Right });

do
	for i, v in next, Locations1 do
		RobberyTeleports:AddButton({ Title = i, Flag = "ExampleButton", Callback = function()
			Teleport(v, "Vehicle")
		end });
	end

	for i, v in next, Locations2 do
		MiscTeleports:AddButton({ Title = i, Flag = "ExampleButton", Callback = function()
			Teleport(v, "Vehicle")
		end });
	end
end

if JB_DEBUG then
	warn("[Jailbreaker Debugging] [Miscellaneous Tab]: Loading Sections & Buttons & Toggles & Text..")
end

--// Miscellaneous Tab

local WebhookSection = Misc:AddSection({ Title = "Webhook Logging" });
local Server = Misc:AddSection({
	Title = "Server",
	Side = LibraryEnum.SectionSide.Right
});
local Website = Misc:AddSection({
	Title = "Website",
	Side = LibraryEnum.SectionSide.Right
});

do
	WebhookSection:AddToggle({
		Title = "Toggled",
		Value = (Settings.WebhookEnabled or false),
		Flag = "ExampleToggle",
		Callback = function(state)
			if state and not Settings.WebhookUrl then 
				Notification_new({
					Text = "Please Enter Webhook URL.",
					Duration = 3
				})
			end
			Settings.WebhookEnabled = state
		end
	});
	WebhookSection:AddToggle({
		Title = "Reward Spinner Notifier",
		Value = (Settings.RewardSpinnerNotifier or false),
		Flag = "ExampleToggle",
		Callback = function(state)
			if state and not Settings.WebhookUrl then
				Notification_new({
					Text = "Please Enter Webhook URL.",
					Duration = 3
				})
			end
			Settings.RewardSpinnerNotifier = state
		end
	})
	local RewardSpinnerItems = WebhookSection:AddDropdown({
		Title = "Reward Spinner Items",
		Flag = "ExampleDrop",
		Items = ItemsType,
		AllowNoValue = true,
		MultiSelect = true,
		Callback = function(value, state)
			print(value, state)
			if state and not table.find(Settings.RewardSpinnerItems, value) then
				table.insert(Settings.RewardSpinnerItems, value)
			elseif not state and table.find(Settings.RewardSpinnerItems, value) then
				table.remove(Settings.RewardSpinnerItems, table.find(Settings.RewardSpinnerItems, value))
			end
		end
	})
	for i, Item in pairs(ItemsType) do
		RewardSpinnerItems:Set(Item, table.find(Settings.RewardSpinnerItems, Item) and true or false)
	end
	WebhookSection:AddBox({
		Title = "Webhook URL",
		Flag = "ExampleBox",
		Value = (Settings.WebhookUrl or "Enter Webhook URL"),
		Type = LibraryEnum.BoxMode.FocusLost,
		Callback = function(input)
			if string.find(input, "discord.com/api/webhook") then
				Settings.WebhookUrl = input
			end
		end
	});

	-- WebhookSection:AddSlider({
	-- 	Title = "Message Update Interval (s)",
	-- 	Value = (Settings.WebhookUpdateInterval or 3),
	-- 	Min = 2,
	-- 	Max = 60,
	-- 	Flag = "ExampleSlider",
	-- 	Float = 1,
	-- 	ShowValue = true,
	-- 	StartName = "Empty",
	-- 	EndName = "Full",
	-- 	Callback = function(value)
	-- 		Settings.WebhookUpdateInterval = value
	-- 	end
	-- });

	--WebhookSection:AddPicker({ Title = "Embed Color", Flag = "ExamplePicker", Callback = function(colour)
	--	Settings.WebhookColor = colour:ToHex()
	--end });

	Website:AddClipboard({
		Title = "Copy Link",
		Flag = "ExampleClipboard",
		Callback = function()
			return "https://jailbreaker.site/";
		end
	});
	Website:AddClipboard({
		Title = "Copy Key",
		Flag = "ExampleClipboard",
		Callback = function()
			return jbv2_key or "Admin";
		end
	});

	Server:AddButton({
		Title = "Switch Server",
		Flag = "ExampleButton",
		Callback = function()
			SwitchServer(Settings.SmallServer)
		end
	});
	Server:AddButton({
		Title = "Rejoin Server",
		Flag = "ExampleButton",
		Callback = function()
			TeleportService:Teleport(game.PlaceId, LocalPlayer)
		end
	});
	Server:AddClipboard({
		Title = "Copy Join Code",
		Flag = "ExampleClipboard",
		Callback = function()
			return "game:GetService('TeleportService'):TeleportToPlaceInstance("..game.PlaceId..", '"..game.JobId.."', game:GetService('Players').LocalPlayer)";
		end
	});
end

SetStatus("Disabled")

if JB_DEVMODE then
	if JB_DEBUG then
		warn("[Jailbreaker Debugging]: Loading Developer Mode Tab..")
	end

	local DevModeTab  = Frame:AddTab({ Title = "Developer Mode Tools" }):Select();
	local LocalPlayerSection = DevModeTab:AddSection({ Title = "LocalPlayer" })
	local ToolsSection = DevModeTab:AddSection({
		Title = "Tools",
		Side = LibraryEnum.SectionSide.Right
	})

	local DevToolsSettings = {}

	do
		LocalPlayerSection:AddSlider({
			Title = "Walk Speed",
			Value = 16,
			Min = 16,
			Max = 120,
			Float = 1,
			ShowValue = true,
			StartName = "Normal",
			EndName = "Fast",
			Callback = function(value)
				DevToolsSettings.WalkSpeed = value
			end
		})
		LocalPlayerSection:AddToggle({
			Title = "Walk Speed Enabled",
			Value = false,
			Callback = function(state)
				DevToolsSettings.WalkSpeedEnabled = state

				if state and DevToolsSettings.WalkSpeed then
					local Signal;
					Signal = Humanoid:GetPropertyChangedSignal("WalkSpeed"):Connect(function()
						if DevToolsSettings.WalkSpeedEnabled then
							Humanoid.WalkSpeed = DevToolsSettings.WalkSpeed
						else
							Signal:Disconnect()
						end
					end)
		
					Humanoid.WalkSpeed = DevToolsSettings.WalkSpeed
				end
			end
		})
		LocalPlayerSection:AddSlider({
			Title = "Jump Power",
			Value = 50,
			Min = 50,
			Max = 500,
			Float = 1,
			ShowValue = true,
			StartName = "Low",
			EndName = "High",
			Callback = function(value)
				Humanoid.JumpPower = value
			end
		})
		LocalPlayerSection:AddToggle({
			Title = "Jump Power Enabled",
			Value = false,
			Callback = function(state)
				if state and DevToolsSettings.JumpPower then
					Humanoid.JumpPower = DevToolsSettings.JumpPower
				else
					Humanoid.JumpPower = 50
				end
			end
		})
	end
end

if getgenv().V2_ServerHop then
	Frame.Open = true;
	if Settings.HideUIOnNewServer then
		Frame.Directory.UI.Enabled = false
	end
else
	if JB_DEBUG then
		warn("[Jailbreaker Debugging]: Showing Changelog..")
	end

	Frame:Changelog(JailbreakerVersion, "https://jailbreaker.site", {
		{
			timestamp = Timestamp..": "..JailbreakerVersion,
			message = Changelog
		},
		-- {
		-- 	timestamp = "[10th August 2023]: V2.1.0",
		-- 	message = "Idk how many f**king sh*ts I fixed & added. Apologise for not pushing update (Brizzy is lazy af)."
		-- },
		-- {
        --     timestamp = "[1st July 2023]: V2.0.8",
        --     message = "Bug Fixes & Dev Commands!"
        -- },
        -- {
        --     timestamp = "[24th June 2023]: V2.0.7",
        --     message = "Improved Jewelry!\nFixed lags when escaping.\nFixed Casino weird teleport patterns.\nAdded auto save robberies toggle.\nAdded auto save UI keybind.\nChanged teleport speed slider to percentage."
        -- },
		-- {
        --     timestamp = "[16th June 2023]: V2.0.6",
        --     message = "Bug Fixes & Crash fixes!"
        -- },
        -- {
        --     timestamp = "[24th June 2023]: V2.0.5",
        --     message = "Script-Ware Mac & IOS Support. Bug Fixes!"
        -- },
		-- {
        --     timestamp = "[3th May 2023]: V2.0.4",
        --     message = "Public Release!"
        -- },
		-- {
        --     timestamp = "[3th May 2023]: V2.0.3",
        --     message = "Bug Fixes!"
        -- },
		-- {
        --     timestamp = "[2th May 2023]: V2.0.2",
        --     message = "Website Added, Bug Fixes!"
        -- },
		-- {
        --     timestamp = "[1st May 2023]: V2.0.1",
        --     message = "UI Added, Bug Fixes!"
        -- },
        -- {
        --     timestamp = "[24th April 2023]: V2.0.0",
        --     message = "Released, Bug Fixes."
        -- }
    });
end
	end)()
else
	oldPrint("[Jailbreaker] [3/3]: Authentication failed. Unexpected response.");
	kick("Authentication failed. Unexpected response.");
	LPH_CRASH()
	return
end