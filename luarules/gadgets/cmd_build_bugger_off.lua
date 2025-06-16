local gadget = gadget ---@type gadget

function gadget:GetInfo()
	return {
		name	= "Builder buggeroff",
		desc	= "Enables busy builders and moving units to buggeroff",
		author  = "Flameink",
		date	= "March 14, 2025",
		version = "1.0",
		license = "GNU GPL, v2 or later",
		layer   = 0,
		enabled = true   --  loaded by default?
	}
end

if not gadgetHandler:IsSyncedCode() then
	return
end
local function printf(value)
	Spring.Echo(value)
end
local function print(value)
	Spring.Echo(value)
end
local shouldNotBuggeroff = {}
local cachedUnitDefs = {}
local cachedBuilderTeams = {}
for unitDefID, unitDef in pairs(UnitDefs) do
	if unitDef.isImmobile or unitDef.speed == 0 then
		shouldNotBuggeroff[unitDefID] = true
	end
	
	cachedUnitDefs[unitDefID] = { radius = unitDef.radius, isBuilder = unitDef.isBuilder, speed = unitDef.speed }
end

local function willBeNearTarget(unitID, tx, ty, tz, seconds, maxDistance)
	local ux, uy, uz = Spring.GetUnitPosition(unitID)
	if not ux then return false end

	local vx, vy, vz = Spring.GetUnitVelocity(unitID)
	if not vx then return false end

	local futureX = ux + vx * seconds * Game.gameSpeed
	local futureY = uy + vy * seconds * Game.gameSpeed
	local futureZ = uz + vz * seconds * Game.gameSpeed

	local dx = futureX - tx
	local dy = futureY - ty
	local dz = futureZ - tz
	return math.diag(dx, dy, dz) <= maxDistance
end

-- Check if unit trajectory enters sphere in [0, seconds]
function WillEnterSphere(unitID, cx, cy, cz, radius, startSeconds, endSeconds)
    local ux, uy, uz = Spring.GetUnitPosition(unitID)
    local vx, vy, vz = Spring.GetUnitVelocity(unitID)

	local futureX = ux + vx * endSeconds * Game.gameSpeed
	local futureY = uy + vy * endSeconds * Game.gameSpeed
	local futureZ = uz + vz * endSeconds * Game.gameSpeed

	local futureX2 = ux + vx * startSeconds * Game.gameSpeed
	local futureY2 = uy + vy * startSeconds * Game.gameSpeed
	local futureZ2 = uz + vz * startSeconds * Game.gameSpeed

	local result = LineIntersectsSphere(futureX2, futureY2, futureZ2, futureX, futureY, futureZ, cx, cy, cz, radius + cachedUnitDefs[Spring.GetUnitDefID(unitID)].radius)
	return result
end

function LineIntersectsSphere(x1, y1, z1, x2, y2, z2, cx, cy, cz, radius)
    local dx, dy, dz = x2 - x1, y2 - y1, z2 - z1
    local fx, fy, fz = x1 - cx, y1 - cy, z1 - cz
	-- printf("Doing it")
-- printf("intersecting: {" .. x1 .. " " .. y1  .. " " .. z1 .. "}{ " .. x2 .. " " .. y2 .. " " .. z2 .. " } {" .. cx .. " " .. cy .. " " .. cz .. " }" .. radius)
    local a = dx*dx + dy*dy + dz*dz
    local b = 2 * (fx*dx + fy*dy + fz*dz)
    local c = fx*fx + fy*fy + fz*fz - radius*radius

    local discriminant = b*b - 4*a*c
    if discriminant < 0 then
        return false -- no intersection
    end

    discriminant = math.sqrt(discriminant)
    local t1 = (-b - discriminant) / (2*a)
    local t2 = (-b + discriminant) / (2*a)

    local result = (t1 >= 0 and t1 <= 1) or (t2 >= 0 and t2 <= 1)
	if math.distance2d(x1, z1, cx, cz) < radius or math.distance2d(x2, z2, cx, cz) < radius then
		-- printf("ehhh")
		result = true
	end

	return result
end

local slowUpdateBuilders 	= {}
local watchedBuilders 		= {}
local builderRadiusOffsets 	= {}
local builderDelayTicks     = {}
local needsUpdate 			= false

local FAST_UPDATE_RADIUS	= 400
-- builders take about this much to enter build stance; determined empirically
local BUILDER_DELAY_SECONDS = 3.3
local BUILDER_BUILD_RADIUS  = 200
local SEARCH_RADIUS_OFFSET  = 400
local BUILDING_RADIUS_TWEAK = 50
local FAST_UPDATE_FREQUENCY = 30
local SLOW_UPDATE_FREQUENCY = 60
local BUGGEROFF_RADIUS_INCREMENT = FAST_UPDATE_FREQUENCY * 0.5
local MAX_BUGGEROFF_RADIUS  = 600

local function shouldIssueBuggeroff(builderTeam, interferingUnitID, x, y, z, radius)
	if Spring.AreTeamsAllied(Spring.GetUnitTeam(interferingUnitID), builderTeam) == false then
		return false
	end

	if shouldNotBuggeroff[Spring.GetUnitDefID(interferingUnitID)] then
		return false
	end

	if WillEnterSphere(interferingUnitID, x, y, z, radius, 1.5, BUILDER_DELAY_SECONDS) then
		return true
	end

	return false
end

function watchBuilder(builderID)
	slowUpdateBuilders[builderID]   = nil
	watchedBuilders[builderID]		= true
	builderRadiusOffsets[builderID] = 0
	builderDelayTicks[builderID]	= 0
end

function removeBuilder(builderID)
	slowUpdateBuilders[builderID]   = nil
	watchedBuilders[builderID]	  	= nil
	builderRadiusOffsets[builderID] = nil
	builderDelayTicks[builderID]	= nil
end

function slowWatchBuilder(builderID)
	watchedBuilders[builderID]	  	= nil
	slowUpdateBuilders[builderID]   = true
	builderRadiusOffsets[builderID] = nil
	builderDelayTicks[builderID]	= nil
	-- Give builder initial slow update right away in case the builder is already close
	needsUpdate = true
end

function rotate90CW(ax, ay, bx, by)
    local dx = ax - bx
    local dy = ay - by
    local rx = bx + dy
    local ry = by - dx
    return rx, ry
end

function gadget:GameFrame(frame)
	if frame % FAST_UPDATE_FREQUENCY ~= 0 then
		return
	end

	local builderTeams = {}
	for builderID, _ in pairs(watchedBuilders) do
		local cmdID, options, tag, targetX, targetY, targetZ =  Spring.GetUnitCurrentCommand(builderID, 1)
		local isBuilding  	= false
		local x, y, z		= Spring.GetUnitPosition(builderID)
		local targetID		= Spring.GetUnitIsBuilding(builderID)
		local builderTeam   = Spring.GetUnitTeam(builderID);
		if targetID then isBuilding = true end
		local visited = {}
		
		if builderRadiusOffsets[builderID] ~= nil and builderRadiusOffsets[builderID] > MAX_BUGGEROFF_RADIUS then
			removeBuilder(builderID)
			printf("Giving up".. builderID)

		elseif cmdID == nil or cmdID > -1 or math.distance2d(targetX, targetZ, x, z) > FAST_UPDATE_RADIUS  then
			slowWatchBuilder(builderID)
			printf("Demote slow " .. builderID)


		elseif math.distance2d(targetX, targetZ, x, z) < BUILDER_BUILD_RADIUS + cachedUnitDefs[-cmdID].radius and isBuilding == false and Spring.GetUnitIsBeingBuilt(builderID) == false then
			local builtUnitDefID	= -cmdID
			local buildRadius		= cachedUnitDefs[builtUnitDefID].radius + BUILDING_RADIUS_TWEAK
			local buggerOffRadius	= cachedUnitDefs[builtUnitDefID].radius + BUILDING_RADIUS_TWEAK + builderRadiusOffsets[builderID]
			local searchRadius		= cachedUnitDefs[builtUnitDefID].radius + SEARCH_RADIUS_OFFSET
			local interferingUnits	= Spring.GetUnitsInCylinder(targetX, targetZ, searchRadius)

			-- Make sure at least one builder per player is never told to move
			if (builderTeams[builderTeam] ~= nil) then
				visited[builderID] = true
			end
			builderTeams[builderTeam] = true
			-- Escalate the radius every update. We want to send units away the minimum distance, but
			-- if there are many units in the way, they may cause a traffic jam and need to clear more room.
			builderRadiusOffsets[builderID] = builderRadiusOffsets[builderID] + BUGGEROFF_RADIUS_INCREMENT

			for _, interferingUnitID in ipairs(interferingUnits) do
				if builderID ~= interferingUnitID and visited[interferingUnitID] == nil and Spring.GetUnitIsBeingBuilt(interferingUnitID) == false  then
					-- Only buggeroff from one build site at a time
					visited[interferingUnitID] = true
					local unitX, _, unitZ = Spring.GetUnitPosition(interferingUnitID)
					local unitRadius =  cachedUnitDefs[Spring.GetUnitDefID(interferingUnitID)].radius 
					if shouldIssueBuggeroff(cachedBuilderTeams[builderID], interferingUnitID, targetX, targetY, targetZ, buildRadius) then
						local sendX, sendZ = math.closestPointOnCircle(targetX, targetZ, buggerOffRadius + unitRadius, unitX, unitZ)

						if  math.distance2d(unitX, unitZ, targetX, targetZ) > buildRadius + unitRadius then
							local rotUX, rotUZ = rotate90CW(sendX, sendZ, targetX, targetZ)
							-- sendX, sendZ =  rotate90CW(sendX, sendZ, targetX, targetZ)
							-- if 
							local ccwX, ccwZ = rotate90CW(sendX, sendZ, targetX, targetZ)
							ccwX, ccwZ = rotate90CW(ccwX, ccwZ, targetX, targetZ)
							ccwX, ccwZ = rotate90CW(ccwX, ccwZ, targetX, targetZ)
							sendX, sendZ = ccwX, ccwZ
							-- printf("{" .. ccwX .. ", " .. ccwZ .."} vs {" .. rotUX .. ", " .. rotUZ .. "}")
							-- print("Distance cw " .. math.distance2d(sendX, sendZ, unitX, unitZ) .. "Distance ccw " .. math.distance2d(rotUX, rotUZ, unitX, unitZ))
							if math.distance2d(sendX, sendZ, unitX, unitZ) > math.distance2d(rotUX, rotUZ, unitX, unitZ) then
								sendX, sendZ = rotUX, rotUZ
							end
						end

						if Spring.TestMoveOrder(Spring.GetUnitDefID(interferingUnitID), sendX, targetY, sendZ) then
							Spring.GiveOrderToUnit(interferingUnitID, CMD.INSERT, {0, CMD.MOVE, CMD.OPT_INTERNAL, sendX, targetY, sendZ}, CMD.OPT_ALT )
						end
					end
				end
			end

		elseif isBuilding then
			-- We want to keep updating in case the builder has got another job nearby
			builderRadiusOffsets[builderID] = 0
		end
	end

	if frame % SLOW_UPDATE_FREQUENCY ~= 0 and not needsUpdate then
		return
	end

	needsUpdate = false
	for builderID, _ in pairs(slowUpdateBuilders) do
		local builderCommands   = Spring.GetUnitCommands(builderID, -1)
		local hasBuildCommand, buildCommandFirst = false, false
		local targetX, targetZ  = 0, 0

		if builderCommands ~= nil then
			for idx, command in ipairs(builderCommands) do
				if command.id < 0 then
					hasBuildCommand = true
					if idx == 1 then
						buildCommandFirst = true
						targetX, targetZ  = command.params[1], command.params[3]
					end
				end
			end
		end

		local isBuilding  = false
		if Spring.GetUnitIsBuilding(builderID) then isBuilding = true end

		local x, _, z = Spring.GetUnitPosition(builderID)
		if hasBuildCommand == false then
			removeBuilder(builderID)
		elseif buildCommandFirst and isBuilding == false and math.distance2d(targetX, targetZ, x, z) <= FAST_UPDATE_RADIUS then
			watchBuilder(builderID)
		end
	end
end

function gadget:MetaUnitAdded(unitID, unitDefID, unitTeam)
	if cachedUnitDefs[unitDefID].isBuilder then
		cachedBuilderTeams[unitID] = unitTeam
	end
end

function gadget:Initialize()
	for _, teamID in ipairs(Spring.GetTeamList()) do
		local unitList = Spring.GetTeamUnits(teamID)
		for _, unitID in ipairs(unitList) do
			gadget:MetaUnitAdded(unitID, Spring.GetUnitDefID(unitID), teamID)
		end
	end
end

function gadget:MetaUnitRemoved(unitID, unitDefID, unitTeam)
	cachedBuilderTeams[unitID] = nil
	if cachedUnitDefs[unitDefID].isBuilder then
		removeBuilder(unitID)
	end
end

function gadget:UnitCommand(unitID, unitDefID, unitTeamID, cmdID, cmdParams, cmdOptions, cmdTag, playerID, fromSynced, fromLua)
	if cachedUnitDefs[unitDefID].isBuilder then
		slowWatchBuilder(unitID)
	end
end
