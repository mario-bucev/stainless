/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

import extraction.xlang.{trees => xt}
import inox.{FlagOptionDef, OptionDef}

import java.io.{DataInputStream, DataOutputStream, File, FileInputStream, FileOutputStream}
import java.nio.file.{Files, Paths}
import scala.util.Try
import scala.util.control.NonFatal

object ExtractionCache {

  def writeExtracted(outputFile: File,
                     unit: xt.UnitDef,
                     classes: Seq[xt.ClassDef],
                     functions: Seq[xt.FunDef],
                     typeDefs: Seq[xt.TypeDef]): Unit = {
    val ser = Serializer(xt)
    import ser.given
    var dos: DataOutputStream = null
    try {
      outputFile.getParentFile.mkdirs()
      outputFile.createNewFile()
      dos = new DataOutputStream(new FileOutputStream(outputFile))
      ser.serialize(unit, dos)
      dos.writeInt(classes.size)
      classes.foreach(cd => ser.serialize(cd, dos))
      dos.writeInt(functions.size)
      functions.foreach(fd => ser.serialize(fd, dos))
      dos.writeInt(typeDefs.size)
      typeDefs.foreach(td => ser.serialize(td, dos))
    } finally {
      if (dos != null) dos.close()
    }
  }

  // TODO: Say important notice about global id
  def readExtracted(inputFile: File): Try[(xt.UnitDef, Seq[xt.ClassDef], Seq[xt.FunDef], Seq[xt.TypeDef])] = {
    val serde = utils.Serializer(xt)
    import serde.given

    var dis: DataInputStream = null
    Try(try {
      dis = new DataInputStream(new FileInputStream(inputFile))
      val unit = serde.deserialize[xt.UnitDef](dis)
      val nbCds = dis.readInt()
      val cds = (0 until nbCds).map(_ => serde.deserialize[xt.ClassDef](dis))
      val nbFds = dis.readInt()
      val fds = (0 until nbFds).map(_ => serde.deserialize[xt.FunDef](dis))
      val nbTds = dis.readInt()
      val tds = (0 until nbTds).map(_ => serde.deserialize[xt.TypeDef](dis))
      (unit, cds, fds, tds)
    } finally {
      if (dis != null) dis.close()
    })
  }
}
