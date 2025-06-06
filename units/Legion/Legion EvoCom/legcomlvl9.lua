return {
	legcomlvl9 = {
		maxacc = 0.18,
		activatewhenbuilt = true,
		autoheal = 30,
		maxdec = 1.125,
		energycost = 100000,
		metalcost = 10000,
		builddistance = 600,
		builder = true,
		buildpic = "LEGCOM.DDS",
		buildtime = 240000,
		cancloak = true,
		cloakcost = 100,
		cloakcostmoving = 1000,
		cancapture = true,
		canmanualfire = true,
		canmove = true,
		capturable = false,
		capturespeed = 1800,
		collisionvolumeoffsets = "0 4 0",
		collisionvolumescales = "37 69 37",
		collisionvolumetype = "CylY",
		corpse = "DEAD",
		energymake = 1375,
		energystorage = 8000,
		explodeas = "commanderExplosion",
		footprintx = 2,
		footprintz = 2,
		hidedamage = true,
    	holdsteady = true,
		icontype = "legcomlvl4",
		idleautoheal = 30,
		idletime = 1800,
		sightemitheight = 40,
		mass = 4900,
		health = 20000,
		maxslope = 20,
		speed = 47.5,
		maxwaterdepth = 35,
		metalmake = 42,
		metalstorage = 500,
		mincloakdistance = 50,
		movementclass = "COMMANDERBOT",
		nochasecategory = "ALL",
		objectname = "Units/legevocom3.s3o",
		pushresistant = Spring.GetModOptions().pushresistant,
		radardistance = 1200,
		radaremitheight = 54,
		reclaimable = false,
		reclaimspeed = 4416,
   		releaseheld  = true,
		script = "Units/legevocom3.cob",
		seismicsignature = 0,
		selfdestructas = "commanderexplosion",
		selfdestructcountdown = 5,
		showplayername = true,
		sightdistance = 600,
		sonardistance = 600,
		terraformspeed = 1500,
		turninplaceanglelimit = 140,
		turninplacespeedlimit = 0.825,
		turnrate = 1148,
		upright = true,
		workertime = 1472,
		buildoptions = {
			"legmoho",
			"legfus",
			"legwin",
			"legadveconv",
			"legadvsol",
			"leggeo",
			"legtide",
			"legadvestore",
			"legamstor",
			"coruwageo",
			"coruwmme",
            "coruwmmm",
			"legaheattank",
			"leginf",
			"legshot",
			"legmrv",
			"leginfestor",
			"legvflak",
			"legflak",
			"coratl",
			"legmed",
            "legdtr",
			"legvcarry",
			"legmg",
			"legjuno",
			"legctl",
			"corenaa",
            "legbastion",
			"legeyes",
			"legavrad",
			"legavjam",
			"legdrag",
			"legarad",
			"legfrad",
            "legstronghold",
            "legforti",
			"legfdrag",
			"leglab",
			"legvp",
			"legap",
			"corsy",
			"leghp",
			"legfhp",
            "cormabm",
            "legkeres",
			"legeshotgunmech",
			"corasp",
			"legnanotc",
			"legnanotcplat",
			"legdeflector",
		},
		customparams = {
			unitgroup = 'builder',
			area_mex_def = "legmex",
			iscommander = true,
			effigy_offset = 1,
			evocomlvl = 9,
			--energyconv_capacity = 70,
			--energyconv_efficiency = 1/70,
			model_author = "Tharsis",
			normaltex = "unittextures/leg_normal.dds",
			paralyzemultiplier = 0.025,
			subfolder = "",
			workertimeboost = 6,
			wtboostunittype = "MOBILE",
			evolution_health_transfer = "percentage",
			evolution_target = "legcomlvl10",
			evolution_condition = "timer",
			evolution_timer = 99999,
			evolution_power_threshold = 800000,
			evolution_power_multiplier = 1,
			combatradius = 0,
			inheritxpratemultiplier = 0.25,
			childreninheritxp = "DRONE BOTCANNON",
			parentsinheritxp = "MOBILEBUILT DRONE BOTCANNON",
			effigy = "comeffigylvl5",
			minimum_respawn_stun = 5,
			distance_stun_multiplier = 1,
			fall_damage_multiplier = 5,--this ensures commander dies when it hits the ground so effigies can trigger respawn.
		},
		featuredefs = {
			dead = {
				blocking = true,
				category = "corpses",
				collisionvolumeoffsets = "0 0 0",
				collisionvolumescales = "47 10 47",
				collisionvolumetype = "CylY",
				damage = 40000,
				energy = 0,
				featuredead = "HEAP",
				featurereclamate = "SMUDGE01",
				footprintx = 2,
				footprintz = 2,
				height = 20,
				hitdensity = 100,
				metal = 3500,
				object = 'Units/legcom_dead.s3o',
				reclaimable = true,
				seqnamereclamate = "TREE1RECLAMATE",
			},
			heap = {
				blocking = false,
				category = "heaps",
				collisionvolumescales = "35.0 4.0 6.0",
				collisionvolumetype = "cylY",
				damage = 5000,
				energy = 0,
				featurereclamate = "SMUDGE01",
				footprintx = 2,
				footprintz = 2,
				height = 4,
				hitdensity = 100,
				metal = 1750,
				object = "Units/arm2X2F.s3o",
				reclaimable = true,
				resurrectable = 0,
				seqnamereclamate = "TREE1RECLAMATE",
				world = "All Worlds",
			},
		},
		sfxtypes = {
			explosiongenerators = {
				[1] = "custom:com_sea_laser_bubbles",
				[2] = "custom:barrelshot-medium",
				[3] = "custom:footstep-medium",
				[4] = "custom:barrelshot-tiny",
			},
			pieceexplosiongenerators = {
				[1] = "deathceg3",
				[2] = "deathceg4",
			},
		},
		sounds = {
			build = "nanlath1",
			canceldestruct = "cancel2",
			capture = "capture1",
			cloak = "kloak1",
			repair = "repair1",
			uncloak = "kloak1un",
			underattack = "warning2",
			unitcomplete = "armcomsel",
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
				[1] = "armcom1",
				[2] = "armcom2",
				[3] = "armcom3",
				[4] = "armcom4",
			},
			select = {
				[1] = "armcomsel",
			},
		},
		weapondefs = {
			armmg_weapon = {
                accuracy = 100,
				areaofeffect = 110,
				avoidfeature = false,
                burnblow = true,
                burst = 2,
				burstrate = 0.2,
				craterareaofeffect = 0,
				craterboost = 0,
				cratermult = 0,
				edgeeffectiveness = 0.15,
				explosiongenerator = "custom:genericshellexplosion-small-t2",
				gravityaffected = "true",
				impulsefactor = 1.8,
				name = "Rapid-Fire Plasma Cannon",
				noselfdamage = true,
				range = 500,
				reloadtime = 0.4,
				soundhit = "xplomed2",
				soundhitwet = "splssml",
				soundstart = "cannon3",
                sprayangle = 500,
				turret = true,
				weapontype = "Cannon",
				weaponvelocity = 600,
				damage = {
					default = 500,
					vtol = 250,
				},
			},
			torpedo = {
				areaofeffect = 75,
				avoidfeature = false,
				avoidfriendly = true,
				burnblow = true,
				burst = 4,
				burstrate = 0.15,
				cegtag = "torpedotrail-tiny",
				collidefriendly = true,
				craterareaofeffect = 0,
				craterboost = 0,
				cratermult = 0,
				edgeeffectiveness = 0.55,
				explosiongenerator = "custom:genericshellexplosion-small-uw",
				flighttime = 1.8,
				impulsefactor = 0.123,
				model = "legtorpedo.s3o",
				name = "MK-IX Torpedo Launcher",
				noselfdamage = true,
				predictboost = 1,
				range = 550,
				reloadtime = 0.8,
				soundhit = "xplodep2",
				soundstart = "torpedo1",
				startvelocity = 230,
				tracks = false,
				turnrate = 2500,
				turret = true,
				waterweapon = true,
				weaponacceleration = 50,
				weapontimer = 3,
				weapontype = "TorpedoLauncher",
				weaponvelocity = 425,
				damage = {
					-- commanders = 375,
					default = 350, --278.4375,
					subs = 175,
				},
			},
			disintegrator = {
				areaofeffect = 36,
				avoidfeature = false,
				avoidfriendly = false,
				avoidground = false,
				bouncerebound = 0,
				cegtag = "dgunprojectile",
				commandfire = true,
				craterboost = 0,
				cratermult = 0.15,
				edgeeffectiveness = 0.15,
				energypershot = 500,
				explosiongenerator = "custom:expldgun",
				firestarter = 100,
				firesubmersed = false,
				impulsefactor = 0,
				name = "Disintegrator",
				noexplode = true,
				noselfdamage = true,
				range = 250,
				reloadtime = 0.9,
				soundhit = "xplomas2",
				soundhitwet = "sizzlexs",
				soundstart = "disigun1",
				soundhitvolume = 36,
				soundstartvolume = 96,
				soundtrigger = true,
				tolerance = 20000,
				turret = true,
				waterweapon = true,
				weapontimer = 4.2,
				weapontype = "DGun",
				weaponvelocity = 300,
				damage = {
					commanders = 0,
					default = 99999,
					scavboss = 1000,
				},
			},
			railgunt2 = {
				--accuracy = 7,
				areaofeffect = 16,
				avoidfeature = false,
				burnblow = false,
                burst = 4,
				burstrate = 0.12,
				cegtag = "railgun",
				collidefriendly = false,
				craterareaofeffect = 0,
				craterboost = 0,
				cratermult = 0,
				duration = 0.12,
				edgeeffectiveness = 0.85,
				explosiongenerator = "custom:plasmahit-sparkonly",
				fallOffRate = 0.2,
				firestarter = 0,
				impulsefactor = 1,
				intensity = 0.8,
				minintensity = 1,
				name = "Railgun",
				noselfdamage = true,
				ownerExpAccWeight = 4.0,
				proximitypriority = 1,
				range = 870,
				reloadtime = 2.2,
				rgbcolor = "0.74 0.64 0.94",
				soundhit = "mavgun3",
				soundhitwet = "splshbig",
				soundstart = "lancefire",
				soundstartvolume = 26,
				thickness = 3,
				tolerance = 6000,
				turret = true,
				weapontype = "LaserCannon",
				weaponvelocity = 3000,
				damage = {
					default = 400,
				},
			},
			botcannon = {
				accuracy = 0.2,
				areaofeffect = 10,
				avoidfeature = false,
				avoidfriendly = false,
				burst = 7,
				burstrate = 0.025,
				collidefriendly = false,
				craterareaofeffect = 116,
				craterboost = 0.1,
				cratermult = 0.1,
				edgeeffectiveness = 0.15,
				energypershot = 4200,
				explosiongenerator = "custom:botrailspawn",
				gravityaffected = "true",
				heightboostfactor = 8,
				hightrajectory = 1,
				impulsefactor = 0.5,
				leadbonus = 0,
				model = "LegionUnitCapsule.s3o",
				movingaccuracy = 600,
				mygravity = 4.8,
				name = "Long range bot cannon",
				noselfdamage = true,
				projectiles = 2,
				range = 700,
				reloadtime = 0.9,
				sprayangle = 2800,
				stockpile = true,
				stockpiletime = 10,
				soundhit = "xplonuk1xs",
				soundhitwet = "splshbig",
				soundstart = "lrpcshot3",
				soundstartvolume = 50,
				turret = true,
				trajectoryheight = 1,
				waterbounce = true,
				bounceSlip = 0.74,
				bouncerebound = 0.5,
				numbounce = 10,
				weapontype = "Cannon",
				weaponvelocity = 2000,
				customparams = {
					spawns_name = "babylegshot babylegheavydrone babylegdrone babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob babyleglob",
					spawns_expire = 25,
					spawns_surface = "LAND", -- Available: "LAND SEA"
					spawns_mode = "random",
					stockpilelimit = 5,
				},
				damage = {
					default = 0,
					shields = 250,
				},
			},
		},
		weapons = {
			[1] = {
				def = "ARMMG_WEAPON",
				onlytargetcategory = "NOTSUB",
				fastautoretargeting = true,
			},
			[2] = {
				badtargetcategory = "VTOL",
				def = "TORPEDO",
				onlytargetcategory = "NOTAIR"
			},
			[3] = {
				def = "disintegrator",
				onlytargetcategory = "NOTSUB",
			},
			[4] = {
				badtargetcategory = "NOTAIR GROUNDSCOUT",
				def = "RAILGUNT2",
				onlytargetcategory = "NOTSUB",
			},
			[5] = {
				badtargetcategory = "VTOL GROUNDSCOUT SHIP",
				def = "BOTCANNON",
				onlytargetcategory = "NOTSHIP",
			},
		},
	},
}
