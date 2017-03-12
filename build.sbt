name := "closedforms"

version := "0.2"

scalaVersion := "2.12.1"

// tests are not thread safe
parallelExecution in Test := false

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"

//retrieveManaged := true


