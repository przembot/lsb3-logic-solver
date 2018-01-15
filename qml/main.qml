import QtQuick 2.7
import QtQuick.Window 2.2
import QtQuick.Controls 1.4

Window {
  id: window
  visible: true
  title: qsTr("LSB3 Logic SAT Solver")
  color: "lightsteelblue"
  width: 800
  height: 600

  Item {
    anchors.centerIn: parent
    // pole tekstowe do wprowadzenia wyrazenia
    Column {
      anchors.centerIn: parent
      Rectangle {
        width: window.width*3/4
        height: input.height
        border.width: 2
        border.color: "black"
        color: "lightgreen"
        TextInput {
          id: input
          width: parent.width
          font.pixelSize: 20
          padding: parent.border.width
          focus: true
          wrapMode: TextInput.Wrap
        }
      }

      // przyciski do wstawiania tekstu
      Row {
        anchors.horizontalCenter: parent.horizontalCenter
        InputButton {
          textDisplayed: "C()"
          onClicked: function() {
            input.cursorPosition -= 1
          }
        }
        InputButton {
          textDisplayed: "~"
        }
        InputButton {
          textDisplayed: "and"
          textInserted: "*"
        }
        InputButton {
          textDisplayed: "or"
          textInserted: "+"
        }
        InputButton {
          textDisplayed: "->"
        }
        InputButton {
          textDisplayed: "<->"
        }
        InputButton {
          textDisplayed: "("
        }
        InputButton {
          textDisplayed: ")"
        }
        InputButton {
          textDisplayed: "1"
          textInserted: "T"
        }
        InputButton {
          textDisplayed: "1/2"
          textInserted: "N"
        }
        InputButton {
          textDisplayed: "0"
          textInserted: "F"
        }
      }

      // przyciski do uruchamiania solvera
      Row {
        anchors.horizontalCenter: parent.horizontalCenter
        Button {
          id: satbutton
          text: "SAT"
          onClicked: runsat(input.text) // wolanie haskella
        }
        Button {
          id: tautbutton
          text: "TAUT"
          onClicked: runtaut(input.text) // wolanie haskella
        }
      }

      TextArea {
        anchors.horizontalCenter: parent.horizontalCenter
        id: resultarea
        width: window.width*3/4
        height: width*3/4
        readOnly: true
        text: result // z haskella
        font.pointSize: 14
      }
    }
  }
}
