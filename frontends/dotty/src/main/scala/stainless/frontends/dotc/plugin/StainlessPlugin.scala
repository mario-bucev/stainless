package stainless
package frontends.dotc
package plugin

import dotty.tools.dotc.plugins._

class StainlessPlugin extends StandardPlugin {
  override val name: String = "Stainless"
  override val description: String = "Inject Stainless verification pipeline"

  def init(options: List[String]): List[PluginPhase] = {
    ???
//    val setting = new Setting(options.headOption)
//    (new PhaseA(setting)) :: (new PhaseB(setting)) :: Nil
  }
}
