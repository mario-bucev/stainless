lazy val basic = (project in file("basic"))
  .enablePlugins(StainlessPlugin)
  .settings(Seq(
    version := "0.1",
    scalaVersion := sys.props("dotty.version")
  ))