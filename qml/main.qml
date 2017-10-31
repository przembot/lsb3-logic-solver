import QtQuick 2.0
import QtQuick.Window 2.2
import QtQuick.Controls 1.4

Window {
  id: window
  visible: true
  title: qsTr("LSB3 Logic SAT Solver")

  // pole tekstowe do wprowadzenia wyrazenia
  Column {
    Rectangle {
      width: window.width*2/3
      height: 50
      border.width: 3
      border.color: "black"
      color: "lightgreen"
      TextInput {
        id: input
        width: parent.width
        height: parent.height
        font.pixelSize: 20
        focus: true
      }
    }

    // przyciski do wstawiania tekstu
    Row {
      Button {
        text: "C()"
        onClicked: function() {
          input.text += "C()"
          input.cursorPosition -= 1
        }
      }
      InputButton {
        textDisplayed: "~"
        textInserted: "~"
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
        textInserted: "->"
      }
      InputButton {
        textDisplayed: "<->"
        textInserted: "<->"
      }
    }

    // przyciski do uruchamiania solvera
    Row {
      Button {
        id: satbutton
        text: "SAT"
      }
      Button {
        id: tautbutton
        text: "TAUT"
      }
    }

    TextArea {
      id: resultarea
      width: 300
      text: "Wyniki operacji.."

    }
  }
}
