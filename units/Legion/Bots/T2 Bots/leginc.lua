return {
	leginc = {
		maxacc = 0.0585,
		maxdec = 0.43125,
		energycost = 46000,
		metalcost = 2300,
		buildpic = "LEGINC.DDS",
		buildtime = 55000,
		canmove = true,
		collisionvolumeoffsets = "0 2 0",
		collisionvolumescales = "60 40 60",
		collisionvolumetype = "Box",
		corpse = "DEAD",
		explodeas = "penetrator",
		footprintx = 3,
		footprintz = 3,
		idleautoheal = 5,
		idletime = 1800,
		mass = 5001,
		health = 9000,
		maxslope = 15,
		speed = 24,
		maxwaterdepth = 23,
		movementclass = "HBOT4",
		nochasecategory = "VTOL",
		objectname = "Units/leginc.s3o",
		script = "Units/leginc_clean.cob",
		seismicsignature = 0,
		selfdestructas = "penetrator",
		sightdistance = 650,
		turninplace = true,
		turninplaceanglelimit = 90,
		turninplacespeedlimit = 0.495,
		turnrate = 120,
		upright = true,
		customparams = {
			unitgroup = 'weapon',
			model_author = "Protar, Tharsis",
			normaltex = "unittextures/leg_normal.dds",
			subfolder = "CorBots/T2",
			techlevel = 2,
		},
		featuredefs = {
			dead = {
				blocking = true,
				category = "corpses",
				collisionvolumeoffsets = "-2.34260559082 -0.241825708008 -1.33148193359",
				collisionvolumescales = "60.9344787598 36.418548584 64.3249511719",
				collisionvolumetype = "Box",
				damage = 4500,
				featuredead = "HEAP",
				footprintx = 3,
				footprintz = 3,
				height = 20,
				metal = 1400,
				object = "Units/leginc_dead.s3o",
				reclaimable = true,
			},
			heap = {
				blocking = false,
				category = "heaps",
				collisionvolumescales = "55.0 4.0 6.0",
				collisionvolumetype = "cylY",
				damage = 2500,
				footprintx = 3,
				footprintz = 3,
				height = 4,
				metal = 550,
				object = "Units/cor3X3A.s3o",
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
			canceldestruct = "cancel2",
			underattack = "warning1",
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
				[1] = "kbcormov",
			},
			select = {
				[1] = "kbcorsel",
			},
		},
		weapondefs = {
			heatraylarge = {
				areaofeffect = 72,
				avoidfeature = false,
				beamtime = 0.033,
				beamttl = 0.033,
				camerashake = 0.1,
				corethickness = 0.3,
				craterareaofeffect = 72,
				craterboost = 0,
				cratermult = 0,
				edgeeffectiveness = 0.15,
				energypershot = 17,
				explosiongenerator = "custom:heatray-large",
				firestarter = 90,
				firetolerance = 300,
				impulsefactor = 0,
				intensity = 5,
				laserflaresize = 6,
				name = "Heavy g2g Sustained Heat Ray",
				noselfdamage = true,
				predictboost = 0,
				--proximitypriority = -1,
				range = 725,
				reloadtime = .033,
				rgbcolor = "1 0.55 0",
				rgbcolor2 = "0.9 1.0 0.5",
				soundhitdry = "flamhit1",
				soundhitwet = "sizzle",
				soundstart = "heatray3burn",
				soundstartvolume = 11,
				soundtrigger = 1,
				thickness = 4.5,
				turret = true,
				weapontype = "BeamLaser",
				weaponvelocity = 1500,
				damage = {
					commanders = 16,
					default = 33,
					vtol = 11,
				},
				customparams = {
					exclude_preaim = true,
					--sweepfire=0.4,--multiplier for displayed dps during the 'bonus' sweepfire stage, needed for DPS calcs
				},
			},
		},
		weapons = {
			[1] = {
				def = "heatraylarge",
				onlytargetcategory = "SURFACE",
				fastautoretargeting = true,
			},
		},
	},
}
