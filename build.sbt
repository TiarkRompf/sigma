name := "closedforms"

version := "0.2"

scalaVersion := "2.12.1"

// tests are not thread safe
parallelExecution in Test := false

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"


// eclipse cdt (C parser)

libraryDependencies += "org.eclipse.cdt" % "core" % "5.11.0.201509131935"

libraryDependencies += "org.eclipse.jdt" % "core" % "3.11.0.v20150602-1242"



//retrieveManaged := true
