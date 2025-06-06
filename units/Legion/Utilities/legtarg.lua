return {
	legtarg = {
		activatewhenbuilt = true,
		buildangle = 4096,
		buildpic = "LEGTARG.DDS",
		buildtime = 8700,
		canrepeat = false,
		collisionvolumeoffsets = "0 0 0",
		collisionvolumescales = "60 101 52",
		collisionvolumetype = "CylY",
		corpse = "DEAD",
		energycost = 7200,
		energyupkeep = 100,
		explodeas = "mediumBuildingExplosionGeneric",
		footprintx = 3,
		footprintz = 3,
		health = 2100,
		idleautoheal = 5,
		idletime = 1800,
		istargetingupgrade = true,
		maxacc = 0,
		maxdec = 0,
		maxslope = 10,
		maxwaterdepth = 0,
		metalcost = 810,
		objectname = "Units/LEGTARG.s3o",
		onoffable = true,
		script = "Units/LEGTARG.cob",
		seismicsignature = 0,
		selfdestructas = "mediumBuildingExplosionGenericSelfd",
		sightdistance = 273,
		yardmap = "ooooooooo",
		customparams = {
			buildinggrounddecaldecayspeed = 30,
			buildinggrounddecalsizex = 6,
			buildinggrounddecalsizey = 6,
			buildinggrounddecaltype = "decals/legtarg_aoplane.dds",
			model_author = "Protar & ZephyrSkies",
			normaltex = "unittextures/leg_normal.dds",
			removestop = true,
			removewait = true,
			subfolder = "Legion/Utilities",
			techlevel = 2,
			unitgroup = "util",
			usebuildinggrounddecal = true,
		},
		featuredefs = {
			dead = {
				blocking = true,
				category = "corpses",
				collisionvolumeoffsets = "0 0 0",
				collisionvolumescales = "60 101 52",
				collisionvolumetype = "CylY",
				damage = 1140,
				featuredead = "HEAP",
				footprintx = 5,
				footprintz = 4,
				height = 20,
				metal = 492,
				object = "Units/legtarg_dead.s3o",
				reclaimable = true,
			},
			heap = {
				blocking = false,
				category = "heaps",
				collisionvolumescales = "85.0 14.0 6.0",
				collisionvolumetype = "cylY",
				damage = 570,
				footprintx = 5,
				footprintz = 4,
				height = 4,
				metal = 197,
				object = "Units/arm4X4A.s3o",
				reclaimable = true,
				resurrectable = 0,
			},
		},
		sfxtypes = {
			pieceexplosiongenerators = {
				[1] = "deathceg2",
				[2] = "deathceg3",
				[3] = "deathceg4",
			},
		},
		sounds = {
			activate = "cmd-on",
			canceldestruct = "cancel2",
			deactivate = "cmd-off",
			underattack = "warning1",
			working = "cmd-on",
			count = {
				[1] = "count6",
				[2] = "count5",
				[3] = "count4",
				[4] = "count3",
				[5] = "count2",
				[6] = "count1",
			},
			select = {
				[1] = "targsel1",
			},
		},
	},
}
