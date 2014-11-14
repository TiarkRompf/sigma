name := "closedforms"

version := "0.2"

scalaVersion := "2.10.2"

scalaOrganization := "org.scala-lang.virtualized"

scalacOptions += "-Yvirtualize"

// tests are not thread safe
parallelExecution in Test := false

libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test"

libraryDependencies += "EPFL" %% "lms" % "0.3-SNAPSHOT"

//retrieveManaged := true


