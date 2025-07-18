val toolkitV = "0.1.28"
val toolkit = "org.typelevel" %% "toolkit" % toolkitV
val toolkitTest = "org.typelevel" %% "toolkit-test" % toolkitV

ThisBuild / scalaVersion := "3.3.6"
libraryDependencies += toolkit
libraryDependencies += (toolkitTest % Test)
libraryDependencies ++= Seq(
  "org.typelevel" %% "kittens" % "3.0.0",
  "org.typelevel" %% "cats-laws" % "2.10.0" % Test,
  "org.typelevel" %% "discipline-core" % "1.5.1" % Test,
  "org.typelevel" %% "discipline-scalatest" % "2.2.0" % Test
)
