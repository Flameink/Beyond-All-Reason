return {
	armaca = {
		blocking = false,
		builddistance = 136,
		builder = true,
		buildpic = "ARMACA.DDS",
		buildtime = 17750,
		canfly = true,
		canmove = true,
		collide = true,
		cruisealtitude = 80,
		energycost = 12000,
		energymake = 10,
		energystorage = 50,
		explodeas = "smallExplosionGeneric-builder",
		footprintx = 2,
		footprintz = 2,
		health = 200,
		hoverattack = true,
		idleautoheal = 5,
		idletime = 1800,
		maxacc = 0.07,
		maxdec = 0.4275,
		maxslope = 10,
		maxwaterdepth = 0,
		metalcost = 340,
		objectname = "Units/ARMACA.s3o",
		radardistance = 50,
		script = "Units/ARMACA.cob",
		seismicsignature = 0,
		selfdestructas = "smallExplosionGenericSelfd-builder",
		sightdistance = 383.5,
		speed = 192,
		terraformspeed = 650,
		turninplaceanglelimit = 360,
		turnrate = 240,
		workertime = 100,
		buildoptions = {
			[1] = "armfus",
			[2] = "armafus",
			[3] = "armckfus",
			[4] = "armageo",
			[5] = "armuwageo",
			[6] = "armgmm",
			[7] = "armmoho",
			[8] = "armmmkr",
			[9] = "armuwadves",
			[10] = "armuwadvms",
			[11] = "armarad",
			[12] = "armveil",
			[13] = "armfort",
			[14] = "armasp",
			[15] = "armfasp",
			[16] = "armtarg",
			[17] = "armsd",
			[18] = "armgate",
			[19] = "armamb",
			[20] = "armpb",
			[21] = "armanni",
			[22] = "armflak",
			[23] = "armmercury",
			[24] = "armemp",
			[25] = "armamd",
			[26] = "armsilo",
			[27] = "armbrtha",
			[28] = "armvulc",
			[29] = "armdf",
			[30] = "armap",
			[31] = "armaap",
			[32] = "armplat",
			[33] = "armshltx",
		},
		customparams = {
			model_author = "FireStorm",
			normaltex = "unittextures/Arm_normal.dds",
			subfolder = "ArmAircraft/T2",
			techlevel = 2,
			unitgroup = "buildert2",
		},
		sfxtypes = {
			crashexplosiongenerators = {
				[1] = "crashing-small",
				[2] = "crashing-small",
				[3] = "crashing-small2",
				[4] = "crashing-small3",
				[5] = "crashing-small3",
			},
			pieceexplosiongenerators = {
				[1] = "airdeathceg3-builder",
				[2] = "airdeathceg4-builder",
				[3] = "airdeathceg2-builder",
			},
		},
		sounds = {
			build = "nanlath1",
			canceldestruct = "cancel2",
			repair = "repair1",
			underattack = "warning1",
			working = "reclaim1",
			cant = {
				[1] = "cantdo4",
			},
			count = {
				[1] = "count6",
				[2] = "count5",
				[3] = "count4",
				[4] = "count3",
				[5] = "count2",
				[6] = "count1",
			},
			ok = {
				[1] = "vtolarmv",
			},
			select = {
				[1] = "vtolarac",
			},
		},
	},
}
